"""Measure a three-tile forward and check absolute error bounds in exact rational arithmetic."""

import json
from fractions import Fraction as F
from math import isqrt

import torch

import flash_kda
import flash_kda_C


def vector(t, query):
    big = (t * 2 + 1) % 3 if query else t % 3
    signs = (t * 5 + 1 if query else t * 3 + t // 3) % 8
    return [(-1 if signs & (1 << j) else 1) * (125 if j == big else 4) for j in range(3)]


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def advance(state, correction, key):
    return [s + correction * k for s, k in zip(state, key, strict=True)]


def radius(x, y):
    """Upper dyadic bound for Euclidean distance; exact when both states coincide."""
    square = sum((a - b) ** 2 for a, b in zip(x, y, strict=True))
    return sqrt_upper(square)


def sqrt_upper(square):
    """Upper dyadic bound for the square root of a nonnegative rational."""
    scaled = square * (1 << 80)
    floor = isqrt(scaled.numerator // scaled.denominator)
    result = F(floor + (floor * floor < scaled), 1 << 40)
    assert square <= result**2
    return result


def words(x, bits):
    dtype = torch.int16 if bits == 16 else torch.int32
    return [int(v) % (1 << bits) for v in x.contiguous().view(dtype).flatten().tolist()]


def inverse_certificate(stored, raw_keys):
    """Form A J - I from the raw-input keys and all 256 device words, including padding."""
    keys = [[F(c * 125, 15641) for c in raw] for raw in raw_keys]
    keys += [[F(0)] * 3 for _ in range(16 - len(keys))]
    observed = [list(map(F, row)) for row in stored.tolist()]
    exact_inverse = []
    residual_sq = F(0)
    error_sq = F(0)
    for i in range(16):
        lower = [dot(keys[i], keys[t]) / 2 for t in range(i)]
        exact_row = []
        for j in range(16):
            ident = int(i == j)
            residual = observed[i][j] - ident + sum(lower[t] * observed[t][j] for t in range(i))
            exact = ident - sum(lower[t] * exact_inverse[t][j] for t in range(i))
            exact_row.append(exact)
            residual_sq += residual**2
            error_sq += (observed[i][j] - exact) ** 2
        exact_inverse.append(exact_row)
    assert error_sq <= 31 * residual_sq

    def upper_millionths(squared):
        scaled = squared * 10**12
        floor = isqrt(scaled.numerator // scaled.denominator)
        return floor + (floor**2 < scaled)

    return dict(
        words_bf16=words(stored, 16),
        frobenius_residual_millionths=upper_millionths(residual_sq),
        frobenius_certificate_millionths=upper_millionths(31 * residual_sq),
        frobenius_error_millionths=upper_millionths(error_sq),
    )


def packed_check(args, a, bias, initial, out, final):
    # Start the audited sequence at a non-tile-aligned offset with a distinct preceding state.
    prefix_length = 7
    prefix = [x[:, :prefix_length].flip([1]).contiguous() for x in args]
    prefix_out = torch.full_like(prefix[0], torch.nan)
    prefix_final = torch.full_like(initial, torch.nan)
    flash_kda.fwd(
        *prefix, 1.0, prefix_out, a, bias, 0.0, initial_state=-initial, final_state=prefix_final
    )
    packed = [torch.cat([p, x], dim=1) for p, x in zip(prefix, args, strict=True)]
    packed_out = torch.full_like(packed[0], torch.nan)
    packed_initial = torch.cat([-initial, initial])
    packed_final = torch.full_like(packed_initial, torch.nan)
    offsets = torch.tensor([0, prefix_length, packed[0].shape[1]], device=out.device)
    flash_kda.fwd(
        *packed,
        1.0,
        packed_out,
        a,
        bias,
        0.0,
        initial_state=packed_initial,
        final_state=packed_final,
        cu_seqlens=offsets,
    )
    expected = torch.cat([prefix_out, out], dim=1)
    assert torch.equal(packed_out.view(torch.int16), expected.view(torch.int16))
    expected_state = torch.cat([prefix_final, final])
    assert torch.equal(packed_final.view(torch.int32), expected_state.view(torch.int32))
    return dict(
        sequence_offsets=offsets.tolist(),
        output_bf16=words(packed_out[0, prefix_length:, 0, 0], 16),
        final_state_fp32=words(packed_final[1, 0, 0, :3], 32),
    )


def run():
    n = 33
    device = "cuda"
    shape = (1, n, 1, 128)
    q, k, v, gate = [torch.zeros(shape, dtype=torch.bfloat16, device=device) for _ in range(4)]
    logits = torch.zeros(shape[:-1], dtype=torch.bfloat16, device=device)
    a = torch.zeros(1, device=device)
    bias = torch.zeros((1, 128), device=device)
    source_q = [vector(t, True) for t in range(n)]
    source_k = [vector(t, False) for t in range(n)]
    values = [(7 * t + 3) % 15 - 7 for t in range(n)]
    for matrix, rows in [(q, source_q), (k, source_k)]:
        matrix[0, :, 0, :3] = torch.tensor(rows, device=device) / 128
    v[0, :, 0, 0] = torch.tensor(values, device=device) / 8
    initial = torch.zeros((1, 1, 128, 128), device=device)
    initial[0, 0, 0, :3] = torch.tensor([0.25, -0.125, 0.0625], device=device)

    carries = [initial]
    for count in [16, 32, n]:
        args = [x[:, :count] for x in (q, k, v, gate, logits)]
        out = torch.full_like(args[0], torch.nan)
        final = torch.full_like(initial, torch.nan)
        flash_kda.fwd(*args, 1.0, out, a, bias, 0.0, initial_state=initial, final_state=final)
        assert (out[..., 1:] == 0).all() and (final[:, :, 1:] == 0).all()
        assert (final[..., 3:] == 0).all()
        carries.append(final)
    size = flash_kda_C.get_workspace_size(n, 1, 1)
    ws = torch.full((size,), 0xA5, dtype=torch.uint8, device=device)
    out2, final2 = torch.full_like(out, torch.nan), torch.full_like(final, torch.nan)
    flash_kda_C.fwd(
        q,
        k,
        v,
        gate,
        logits,
        1.0,
        out2,
        ws,
        a,
        bias,
        0.0,
        initial_state=initial,
        final_state=final2,
    )
    assert torch.equal(out2, out) and torch.equal(final2, final)
    tiles = 3
    kd = ws[: tiles * 4096].view(torch.bfloat16).reshape(tiles, 16, 128)
    offset = tiles * (3 * 4096 + 512)
    inv = ws[offset : offset + tiles * 512].view(torch.bfloat16).reshape(tiles, 16, 16)
    normalizer = F(15641, 16000)
    observed = list(map(F, out[0, :, 0, 0].tolist()))

    def row(state):
        return list(map(F, state[0, 0, 0, :3].tolist()))

    exact_state = row(initial)
    accumulated = F(0)
    worst_actual = worst_bound = F(0)
    weighted_sum = gap_sum = worst_weighted_bound = F(0)
    records = []
    for b in range(tiles):
        start = 16 * b
        count = min(16, n - start)
        # Candidate corrections from the stored preparation arrays and a public prefix state.
        padded = torch.zeros_like(kd[b])
        padded[:count] = v[0, start : start + count, 0]
        entering = carries[b][0, 0].to(torch.bfloat16)
        predicted = torch.mm(kd[b], entering.t(), out_dtype=torch.float32)
        rhs = ((padded.float() - predicted) / 2).to(torch.bfloat16)
        corrections = torch.mm(inv[b], rhs)
        assert (corrections[:, 1:] == 0).all()
        reconstructed = row(carries[b])
        for j, correction in enumerate(map(F, corrections[:count, 0].tolist())):
            t = start + j
            raw_query, raw_key = [[F(c, 128) for c in rows[t]] for rows in (source_q, source_k)]
            for raw in (raw_query, raw_key):
                assert dot(raw, raw) + F(1, 10**6) == normalizer**2
            query, key = [[c / normalizer for c in raw] for raw in (raw_query, raw_key)]
            value = F(values[t], 8)
            residual = correction - (value - dot(reconstructed, key)) / 2
            reconstructed = advance(reconstructed, correction, key)
            accumulated += abs(residual)  # normalized key length <= 1
            readout_gap = abs(observed[t] - dot(reconstructed, query))
            bound = accumulated + readout_gap
            # With strength one half, a value perturbation of twice the residual absorbs it.
            weighted_sum += 2 * residual**2
            weighted_bound = gap_sum + sqrt_upper(weighted_sum) + readout_gap
            worst_weighted_bound = max(worst_weighted_bound, weighted_bound)
            exact_state = advance(exact_state, (value - dot(exact_state, key)) / 2, key)
            actual = abs(observed[t] - dot(exact_state, query))
            assert actual <= min(bound, weighted_bound)
            worst_actual, worst_bound = max(worst_actual, actual), max(worst_bound, bound)
        gap = radius(row(carries[b + 1]), reconstructed)
        accumulated += gap
        gap_sum += gap
        records.append(
            dict(
                correction_bf16=words(corrections[:count, 0], 16),
                inverse=inverse_certificate(inv[b], source_k[start : start + count]),
                measured_exit_fp32=words(carries[b + 1][0, 0, 0, :3], 32),
                exit_gap_upper=str(gap),
            )
        )
    final_error = radius(row(final), exact_state)
    weighted_final = gap_sum + sqrt_upper(weighted_sum)
    assert final_error <= min(accumulated, weighted_final)

    def ceil_million(x):
        return -(-x.numerator * 10**6 // x.denominator)

    return dict(
        device=torch.cuda.get_device_name(),
        sequence_length=n,
        query_numerators=source_q,
        key_numerators=source_k,
        value_numerators=values,
        initial_state_fp32=words(initial[0, 0, 0, :3], 32),
        packed=packed_check((q, k, v, gate, logits), a, bias, initial, out, final),
        output_bf16=words(out[0, :, 0, 0], 16),
        tiles=records,
        millionths=dict(
            max_output_certificate=ceil_million(worst_bound),
            final_state_certificate=ceil_million(accumulated),
            max_output_weighted_certificate=ceil_million(worst_weighted_bound),
            final_state_weighted_certificate=ceil_million(weighted_final),
            max_output_exact_error=ceil_million(worst_actual),
            final_state_exact_error_upper=ceil_million(final_error),
        ),
    )


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
