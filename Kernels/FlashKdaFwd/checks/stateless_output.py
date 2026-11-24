"""Run a 33-token counterexample using the public API with both state arguments omitted."""

import json

import torch

import flash_kda
from torch_ref import torch_ref
from reference_operands import record_reference_fma


def inputs(first_update_logit, small_key):
    shape = (1, 33, 1, 128)
    options = dict(dtype=torch.bfloat16, device="cuda")
    q, k, v, g = (torch.zeros(shape, **options) for _ in range(4))
    strength = torch.zeros(shape[:-1], **options)
    k[0, 15, 0, 0], v[0, 15, 0, 0] = 1, 3
    strength[0, 15, 0] = first_update_logit
    k[0, 31, 0, 0], k[0, 31, 0, 1] = small_key, 1
    q[0, 32, 0, 0] = 1
    g.fill_(-40)
    g[0, 31] = 0
    param, bias = torch.zeros(1, device="cuda"), torch.zeros((1, 128), device="cuda")
    bound = float.fromhex("-0x1.934420p-1")
    return (q, k, v, g, strength, 1.0), (param, bias, bound)


def run(first_update_logit, small_key):
    args, gates = inputs(first_update_logit, small_key)
    outputs = []
    with record_reference_fma() as operands:
        for forward in (flash_kda.fwd, torch_ref):
            out = torch.full_like(args[0], -7)
            forward(*args, out, *gates)
            assert out.nonzero().tolist() == [[0, 32, 0, 0]]
            outputs.append(out[0, 32, 0, 0].item())
    return dict(
        first_update_logit=first_update_logit,
        small_key=small_key,
        kernel_output=outputs[0],
        reference_output=outputs[1],
        reference_fma_operands=operands,
    )


if __name__ == "__main__":
    cases = [run(2.0**-16, 2.0**-28), run(0, 2.0**-28), run(2.0**-16, 0)]
    for case in cases[:2]:
        assert (case["kernel_output"], case["reference_output"]) == (129 / 128, 65 / 64)
    assert cases[2]["kernel_output"] == cases[2]["reference_output"] == 65 / 64
    print(json.dumps({"device": torch.cuda.get_device_name(), "cases": cases}, indent=2))
