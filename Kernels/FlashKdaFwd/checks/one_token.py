"""Compare a one-token forward call and read the two compiled kernels' shared workspace."""

import json
import math
from fractions import Fraction

import torch

import flash_kda
import flash_kda_C
from torch_ref import torch_ref


def exact_words(t):
    return [f"0x{x & 0xFFFF:04x}" for x in t.view(torch.int16).flatten().tolist()]


def run(d, scale):
    shape = (1, 1, 1, 128)
    q, k, v, g = (torch.zeros(shape, device="cuda", dtype=torch.bfloat16) for _ in range(4))
    q.flatten()[:4] = torch.tensor([1, 1, -1, -d])
    k.flatten()[:4] = torch.tensor([0.25, 0.5, 0.75, d])
    v.flatten()[0] = 1
    beta = torch.zeros(shape[:-1], device="cuda", dtype=torch.bfloat16)
    a = torch.zeros(1, device="cuda")
    bias = torch.zeros((1, 128), device="cuda")
    outputs = []
    for forward in (flash_kda.fwd, torch_ref):
        out = torch.full_like(q, -7)
        forward(q, k, v, g, beta, scale, out, a, bias, 0.0)
        assert (out.flatten()[1:] == 0).all()
        outputs.append(out)
    assert torch.equal(*outputs)
    size = flash_kda_C.get_workspace_size(1, 1, 1)
    workspace = torch.full((size,), 0xA5, device="cuda", dtype=torch.uint8)
    internal_out = torch.full_like(q, -7)
    flash_kda_C.fwd(q, k, v, g, beta, scale, internal_out, workspace, a, bias, 0.0)
    assert torch.equal(internal_out, outputs[0])
    # For one tile the three 16-by-128 bfloat16 matrices are followed by 128 floats
    # and the inverse and query-key product (each a 16-by-16 bfloat16 matrix).
    kd, qd, kr = [workspace[i * 4096 : (i + 1) * 4096].view(torch.bfloat16) for i in range(3)]
    mqk = workspace[3 * 4096 + 512 + 512 : 3 * 4096 + 512 + 1024].view(torch.bfloat16)
    assert torch.equal(kd, kr)
    assert (kd[4:] == 0).all() and (qd[4:] == 0).all() and (mqk[1:] == 0).all()
    stored_dot = sum(Fraction(x.item()) * Fraction(y.item()) for x, y in zip(qd[:4], kd[:4]))
    ideal = -scale * d * d / (2 * math.sqrt((3 + d * d + 1e-6) * (0.875 + d * d + 1e-6)))
    return dict(
        fourth_magnitude=d,
        scale=scale,
        exact_real_approx=ideal,
        kernel=outputs[0].flatten()[0].item(),
        reference=outputs[1].flatten()[0].item(),
        normalized_query_words=exact_words(qd[:4]),
        normalized_key_words=exact_words(kd[:4]),
        exact_dot_of_workspace_inputs=str(stored_dot),
        stored_dot_word=exact_words(mqk[:1])[0],
        stored_dot=mqk[0].item(),
        output_word=exact_words(internal_out.flatten()[:1])[0],
    )


if __name__ == "__main__":
    cases = [run(0, 1.0), run(1 / 32, 1.0), run(1 / 64, 1.0), run(1 / 32, 1 / math.sqrt(128))]
    assert cases[0]["exact_real_approx"] == 0 and cases[0]["kernel"] > 0
    assert all(case["exact_real_approx"] < 0 < case["kernel"] for case in cases[1:])
    print(json.dumps(dict(device=torch.cuda.get_device_name(), cases=cases), indent=2))
