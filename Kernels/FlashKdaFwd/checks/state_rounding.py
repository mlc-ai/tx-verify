"""Compare the compiled public forward entry with the upstream mixed-precision reference."""

import json
import math

import torch

import flash_kda
from torch_ref import torch_ref
from reference_operands import bits, record_reference_fma


def run(name, lengths, initial, key, bound, *, read_next_tile=False):
    total = sum(lengths)
    nseq = len(lengths)
    offsets = None
    if nseq > 1:
        offsets = torch.tensor([0, *torch.tensor(lengths).cumsum(0).tolist()], dtype=torch.int64)
    shape = (1, total, 1, 128)
    q, k, v, g = (torch.zeros(shape, dtype=torch.bfloat16) for _ in range(4))
    if read_next_tile:
        # Token 16 updates the state. Token 17 reads its rounded bfloat16 copy.
        assert lengths == [17]
        k[0, 15, 0, 0], k[0, 15, 0, 1] = key, 1
        q[0, 16, 0, 0] = 1
        g.fill_(-40)
        g[0, 15] = 0
    else:
        k[..., 0] = key
        k[..., 1] = 1 if key else 0
    beta = torch.zeros(shape[:-1], dtype=torch.bfloat16)
    param, bias = torch.zeros(1), torch.zeros((1, 128))
    state = torch.zeros((nseq, 1, 128, 128))
    state[..., 0, 0] = initial
    state[..., 2, 2] = 1
    out, expected_out = torch.full_like(q, -7), torch.full_like(q, -7)
    final, expected_state = torch.full_like(state, -7), torch.full_like(state, -7)
    args = q, k, v, g, beta, 1.0
    flash_kda.fwd(*args, out, param, bias, bound, state, final, offsets)
    with record_reference_fma() as operands:
        torch_ref(*args, expected_out, param, bias, bound, state, expected_state, offsets)
    torch.cuda.synchronize()
    mismatch = final.view(torch.int32) != expected_state.view(torch.int32)
    output_mismatch = out.view(torch.int16) != expected_out.view(torch.int16)
    assert (out != -7).all() and (expected_out != -7).all()
    if read_next_tile:
        assert all(pos == [0, 16, 0, 0] for pos in output_mismatch.nonzero().tolist())
    else:
        assert (out == 0).all() and (expected_out == 0).all()
    assert (final != -7).all() and (expected_state != -7).all()
    assert all(pos[1:] == [0, 0, 0] for pos in mismatch.nonzero().tolist())
    return dict(
        name=name,
        lengths=lengths,
        gate_lower_bound=bound.hex(),
        first_kernel_state=[bits(x) for x in final[:, 0, 0, 0]],
        first_reference_state=[bits(x) for x in expected_state[:, 0, 0, 0]],
        differing_state_elements=mismatch.sum().item(),
        differing_output_elements=output_mismatch.sum().item(),
        last_kernel_output=bits(out[0, -1, 0, 0]),
        last_reference_output=bits(expected_out[0, -1, 0, 0]),
        reference_fma_operands=operands,
    )


if __name__ == "__main__":
    torch.set_default_device("cuda")
    # This bound gives exactly 3/4 in the public implementation for one token with gate zero.
    bound = float.fromhex("-0x1.269620p-1")
    initial = 1.5 + 2.0**-22
    tie_initial = float.fromhex("0x1.595554p+0")  # binary32 bits 0x3facaaaa
    tests = [
        run("normal operands", [1], initial, 2.0**-28, bound),
        run("packed independent sequences", [1, 0, 1], initial, 2.0**-28, bound),
        run("zero correction control", [1], initial, 0, bound),
        run("normal input, subnormal result", [1], 2.0**-126, 0, -math.log(4)),
        run("normal result control", [1], 2.0**-125, 0, -math.log(4)),
        run("output after tile boundary", [17], tie_initial, 2.0**-28, bound, read_next_tile=True),
        run("tile boundary control", [17], tie_initial, 0, bound, read_next_tile=True),
    ]
    assert [case["differing_state_elements"] for case in tests] == [1, 2, 0, 1, 0, 1, 0]
    for index in (0, 1):
        case = tests[index]
        for n, gpu, ref in zip(
            case["lengths"], case["first_kernel_state"], case["first_reference_state"], strict=True
        ):
            assert (gpu, ref) == (("0x3f900001", "0x3f900002") if n else ("0x3fc00002",) * 2)
        assert all(
            values == ["0x3fc00002", "0x3f400000", "0xa3100000"]
            for values in case["reference_fma_operands"]
        )
    assert tests[3]["first_kernel_state"] == ["0x00000000"]
    assert tests[3]["first_reference_state"] == ["0x00400000"]
    assert tests[5]["last_kernel_output"] == "0x3f81"
    assert tests[5]["last_reference_output"] == "0x3f82"
    assert [case["differing_output_elements"] for case in tests] == [0, 0, 0, 0, 0, 1, 0]
    print(json.dumps({"device": torch.cuda.get_device_name(), "cases": tests}, indent=2))
