"""Find the best bfloat16 outputs for two exact single-token calls and optionally run them."""

import argparse
from collections import Counter
from fractions import Fraction
import json


def finite_word(word):
    exponent = (word >> 7) & 255
    fraction = word & 127
    if exponent == 255:
        return None
    if exponent == 0:
        magnitude = Fraction(fraction, 2**133)
    else:
        magnitude = (128 + fraction) * Fraction(2) ** (exponent - 134)
    return -magnitude if word & 0x8000 else magnitude


def closest(target):
    best = None
    winners = []
    for word in range(2**16):
        value = finite_word(word)
        if value is None:
            continue
        error = abs(value - target)
        if best is None or error < best:
            best = error
            winners = [word]
        elif error == best:
            winners.append(word)
    return {
        "exact_output": str(target),
        "closest_finite_words": [f"0x{word:04x}" for word in winners],
        "minimum_absolute_error": str(best),
        "minimum_relative_error": str(best / target),
    }


def gpu_outputs(small):
    import flash_kda
    import torch

    shape = (1, 1, 1, 128)
    q, k, gate = [torch.zeros(shape, dtype=torch.bfloat16, device="cuda") for _ in range(3)]
    strength = torch.zeros(shape[:-1], dtype=torch.bfloat16, device="cuda")
    param = torch.zeros(1, device="cuda")
    bias = torch.zeros((1, 128), device="cuda")
    q[..., 0] = 1
    k[..., 1 if small else 0] = 1
    if small:
        q[..., 2] = 2.0**-67
        k[..., 2] = 2.0**-67
        assert q[..., 2].view(torch.int16).item() == k[..., 2].view(torch.int16).item() == 0x1E00
    value = torch.full_like(q, 1.0 if small else 2.0**127)
    assert value.view(torch.int16).unique().tolist() == ([0x3F80] if small else [0x7F00])
    results = {}
    for mode in ("fixed", "packed"):
        offsets = (
            torch.tensor([0, 1], dtype=torch.int64, device="cuda") if mode == "packed" else None
        )
        out = torch.full_like(q, -7)
        flash_kda.fwd(
            q,
            k,
            value,
            gate,
            strength,
            1.0 if small else 8.0,
            out,
            param,
            bias,
            -1.0,
            cu_seqlens=offsets,
        )
        words = Counter(x & 0xFFFF for x in out.view(torch.int16).flatten().tolist())
        results[mode] = {f"0x{w:04x}": count for w, count in sorted(words.items())}
    return results


def main(gpu):
    epsilon = Fraction(1, 1_000_000)
    overlap = Fraction(1, 2**134)
    targets = {
        "small": overlap / (2 * (1 + overlap + epsilon)),
        "large": Fraction(2**129, 1 + epsilon),
    }
    records = {name: closest(target) for name, target in targets.items()}
    assert records["small"]["closest_finite_words"] == ["0x0000", "0x8000"]
    assert records["small"]["minimum_relative_error"] == "1"
    assert records["large"]["closest_finite_words"] == ["0x7f7f"]
    if gpu:
        for name, record in records.items():
            record["public_outputs"] = gpu_outputs(name == "small")
    print(json.dumps(records, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--gpu", action="store_true", help="also inspect the public forward outputs"
    )
    main(parser.parse_args().gpu)
