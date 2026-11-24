"""Check the public forward entry on finite, exactly specified 16-token inputs."""

import argparse
import json

import torch

import flash_kda


def words(tensor):
    width = tensor.element_size() * 8
    dtype = {16: torch.int16, 32: torch.int32}[width]
    return [hex(w & ((1 << width) - 1)) for w in tensor.view(dtype).unique().tolist()]


def gate_overflow_modes(inputs, state, expected_output, expected_state):
    q, k, v, gate, strength, param, bias = inputs
    offsets = torch.tensor([0, q.shape[1]], device=q.device, dtype=torch.int64)
    records = []
    for packed in (False, True):
        for has_initial in (False, True):
            for has_final in (False, True):
                out = torch.full_like(q, -7)
                final = torch.full_like(state, -7) if has_final else None
                flash_kda.fwd(
                    q,
                    k,
                    v,
                    gate,
                    strength,
                    1.0,
                    out,
                    param,
                    bias,
                    -5.0,
                    initial_state=state if has_initial else None,
                    final_state=final,
                    cu_seqlens=offsets if packed else None,
                )
                out_words = words(out)
                state_words = words(final) if has_final else []
                assert out_words == expected_output
                assert not has_final or state_words == expected_state
                records.append(
                    dict(
                        packed=packed,
                        initial_state=has_initial,
                        final_state=has_final,
                        output_words=out_words,
                        state_words=state_words,
                    )
                )
    return records


def run(name, log_parameter, query_value, reference):
    shape = (1, 16, 1, 128)
    q, k, v, gate = (torch.zeros(shape, dtype=torch.bfloat16, device="cuda") for _ in range(4))
    q[..., 0] = query_value
    strength = torch.zeros(shape[:-1], dtype=torch.bfloat16, device="cuda")
    param = torch.full((1,), float(log_parameter), dtype=torch.float32, device="cuda")
    bias = torch.zeros((1, 128), dtype=torch.float32, device="cuda")
    state = torch.zeros((1, 1, 128, 128), dtype=torch.float32, device="cuda")
    if query_value:
        state[..., 0, 0] = 1
    assert all(x.isfinite().all() for x in (q, k, v, gate, strength, param, bias, state))
    out = torch.full_like(q, -7)
    final = torch.full_like(state, -7)
    # A zero bound removes all state decay in the nonzero-query examples.
    bound = 0.0 if query_value else -5.0
    flash_kda.fwd(q, k, v, gate, strength, 1.0, out, param, bias, bound, state, final)
    torch.cuda.synchronize()
    theoretical = query_value / (query_value**2 + 1e-6) ** 0.5 if query_value else 0.0
    result = dict(
        name=name,
        log_parameter=log_parameter,
        query_value=query_value,
        real_formula_evaluated_in_float64=theoretical,
        first_output=str(out.flatten()[0].item()),
        first_final=str(final.flatten()[0].item()),
        nonzero_output=torch.count_nonzero(out).item(),
        state_changed=(final != state).sum().item(),
        nonzero_query_output=torch.count_nonzero(out[..., 0]).item(),
        nan_output=out.isnan().sum().item(),
        nan_state=final.isnan().sum().item(),
        written_output=int((out != -7).sum().item()),
        written_state=int((final != -7).sum().item()),
    )

    if result["nan_output"]:
        result["unique_output_words"] = words(out)
        result["unique_final_words"] = words(final)
        result["launch_modes"] = gate_overflow_modes(
            (q, k, v, gate, strength, param, bias),
            state,
            result["unique_output_words"],
            result["unique_final_words"],
        )

    if reference is not None:
        ref_out = torch.full_like(q, -7)
        ref_state = torch.full_like(state, -7)
        reference(q, k, v, gate, strength, 1.0, ref_out, param, bias, bound, state, ref_state)
        # Compare raw bits so that NaN payloads and signed zeros are included.
        result["reference_output_bit_mismatches"] = (
            (out.view(torch.int16) != ref_out.view(torch.int16)).sum().item()
        )
        result["reference_state_bit_mismatches"] = (
            (final.view(torch.int32) != ref_state.view(torch.int32)).sum().item()
        )
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--reference", action="store_true", help="also run upstream tests/torch_ref.py"
    )
    reference = None
    if parser.parse_args().reference:
        from torch_ref import torch_ref as reference

    results = [
        run("zero control", 0, 0, reference),
        run("unit query control", 0, 1, reference),
        run("finite gate parameter", 100, 0, reference),
        run("finite query norm", 0, 2.0**64, reference),
    ]
    assert (results[0]["nonzero_output"], results[0]["state_changed"]) == (0, 0)
    assert results[1]["first_output"] == "1.0" and results[1]["state_changed"] == 0
    assert results[1]["nonzero_output"] == results[1]["nonzero_query_output"] == 16
    assert (results[2]["nan_output"], results[2]["nan_state"]) == (2048, 16384)
    assert (results[3]["nonzero_output"], results[3]["state_changed"]) == (0, 0)
    assert all((r["written_output"], r["written_state"]) == (2048, 16384) for r in results)
    print(
        json.dumps(
            {
                "device": torch.cuda.get_device_name(),
                "capability": torch.cuda.get_device_capability(),
                "results": results,
            },
            indent=2,
        )
    )
