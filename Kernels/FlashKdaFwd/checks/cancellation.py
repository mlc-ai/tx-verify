"""Check the effect of the bfloat16 state view for a well-scaled finite public input."""

import json
import math

import torch
import flash_kda
from torch_ref import torch_ref


def run(increment):
    shape = (1, 1, 1, 128)
    q, k, v, g = (torch.zeros(shape, dtype=torch.bfloat16, device="cuda") for _ in range(4))
    q[..., :2] = 1
    strength = torch.zeros(shape[:-1], dtype=q.dtype, device=q.device)
    state = torch.zeros((1, 1, 128, 128), device=q.device)
    state[0, 0, 0, 0], state[0, 0, 0, 1] = 1 + increment, -1
    gate_param, bias = torch.zeros(1, device=q.device), torch.zeros((1, 128), device=q.device)
    outputs = []
    for impl in (flash_kda.fwd, torch_ref):
        out, final = torch.full_like(q, -7), torch.full_like(state, -7)
        impl(q, k, v, g, strength, 1.0, out, gate_param, bias, 0.0, state, final)
        assert torch.equal(final, state) and (out[..., 1:] == 0).all()
        outputs.append(out.flatten()[0].item())
    return dict(
        increment=increment,
        kernel=outputs[0],
        upstream_reference=outputs[1],
        real_output_in_float64=increment / math.sqrt(2 + 1e-6),
    )


if __name__ == "__main__":
    cases = [run(2.0**-9), run(2.0**-7)]
    assert cases[0]["kernel"] == cases[0]["upstream_reference"] == 0.0
    assert cases[1]["kernel"] == cases[1]["upstream_reference"] > 0
    print(json.dumps({"device": torch.cuda.get_device_name(), "cases": cases}, indent=2))
