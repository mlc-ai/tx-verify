"""Apply FlashKDA's upstream exact and tolerance checks to the same finite input."""

import json
import struct
from pathlib import Path

import torch

import fla
from fla.utils import assert_close, get_abs_err, get_err_ratio
from test_fwd import run_fla_gold_reference, run_flash_kda_batched
from torch_ref import torch_ref


def binary32(x):
    return f"0x{struct.unpack('>I', struct.pack('>f', x))[0]:08x}"


def compare_rejected(gold, candidate, limit, label):
    try:
        assert_close(label, gold, candidate, limit)
    except AssertionError as exc:
        rejection = str(exc)
        assert "diff:" in rejection and "ratio:" in rejection, rejection
    else:
        raise AssertionError("the published output tolerance unexpectedly accepted the tensors")
    return dict(
        abs_max=get_abs_err(gold, candidate),
        rms_ratio=get_err_ratio(gold, candidate),
        assertion=rejection.strip(),
    )


def run(packed):
    # The packed case contains an independent all-zero one-token sequence after the witness.
    length = 34 if packed else 33
    options = dict(dtype=torch.bfloat16, device="cuda")
    q, k, v, g = (torch.zeros((1, length, 2, 128), **options) for _ in range(4))
    beta = torch.zeros((1, length, 2), **options)
    param = torch.zeros(2, device="cuda")
    bias = torch.zeros(2, 128, device="cuda")
    lower = float.fromhex("-0x1.934420p-1")
    g.fill_(-40)
    g[0, 31, 0] = 0
    k[0, 15, 0, 0], v[0, 15, 0, 0] = 1, 3
    beta[0, 15, 0] = 2**-16
    k[0, 31, 0, 0], k[0, 31, 0, 1] = 2**-28, 1
    q[0, 32, 0, 0] = 1
    q[0, 0, 1, :4] = torch.tensor([1, 1, -1, -1 / 32])
    k[0, 0, 1, :4] = torch.tensor([1 / 4, 1 / 2, 3 / 4, 1 / 32])
    v[0, 0, 1] = 1024
    offsets = torch.tensor([0, 33, 34], device="cuda") if packed else None
    initial = torch.zeros((2 if packed else 1, 2, 128, 128), device="cuda")
    args = (q, k, v, g, beta, initial, param, bias, 1.0, lower, offsets)
    production, _ = run_flash_kda_batched(*args)
    gold, _, _, _ = run_fla_gold_reference(*args)
    mixed = torch.full_like(q, torch.nan)
    torch_ref(
        q,
        k,
        v,
        g,
        beta,
        1.0,
        mixed,
        param,
        bias,
        lower,
        initial_state=initial.to(torch.bfloat16),
        final_state=torch.empty_like(initial, dtype=torch.bfloat16),
        cu_seqlens=offsets,
    )
    markers = {}
    for name, tensor in [
        ("production", production),
        ("torch_reference", mixed),
        ("fla_reference", gold),
    ]:
        first = tensor[0, 0, 1, 0].item()
        last = tensor[0, 32, 0, 0].item()
        pattern = torch.zeros_like(tensor)
        pattern[0, 0, 1] = first
        pattern[0, 32, 0, 0] = last
        assert torch.equal(pattern, tensor) and first != 0 and last != 0
        markers[name] = [binary32(first), binary32(last)]
    # These are the six decoded reference and output words used by the Lean tensor proof.
    assert markers == {
        "production": ["0x3e8a0000", "0x3f810000"],
        "torch_reference": ["0x3e8a0000", "0x3f820000"],
        "fla_reference": ["0xbe9de400", "0x3f818038"],
    }
    mismatches = (production != mixed).nonzero().tolist()
    assert not torch.equal(production, mixed) and mismatches == [[0, 32, 0, 0]]
    limit = 0.006 if packed else 0.005
    return dict(
        token_count=length,
        cumulative_lengths=offsets.tolist() if packed else None,
        output_words_as_binary32=markers,
        exact_mismatch_indices=mismatches,
        comparison_threshold=limit,
        **compare_rejected(gold, production, limit, "output"),
        reference_comparison=compare_rejected(gold, mixed, limit, "torch reference"),
    )


if __name__ == "__main__":
    import subprocess

    root = Path(fla.__file__).resolve().parents[1]
    commit = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True
    ).strip()
    assert commit == "3a9ce1c83a13994d824dbb3421e2989d330bb38b"
    with torch.inference_mode():
        cases = [run(False), run(True)]
    print(
        json.dumps(
            dict(device=torch.cuda.get_device_name(), fla_commit=commit, cases=cases), indent=2
        )
    )
