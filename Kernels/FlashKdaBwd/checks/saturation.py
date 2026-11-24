# SPDX-License-Identifier: Apache-2.0
"""Measure the logit gradient in a one-token call to FLA's public autograd function."""

import argparse
import json
import math
from pathlib import Path

import torch
from fla.ops.common.gate import fused_beta_sigmoid_bwd_kernel
from fla.ops.kda import chunk_kda
from provenance import environment


def run(logit):
    shape = (1, 1, 1, 128)
    q = torch.zeros(shape, dtype=torch.bfloat16, device="cuda")
    q[..., 0] = 1
    v = torch.zeros_like(q)
    v[..., 0] = 2**30
    g = torch.zeros_like(q)
    beta = torch.full(shape[:-1], logit, dtype=q.dtype, device=q.device, requires_grad=True)
    param = torch.zeros(1, device=q.device)
    bias = torch.zeros(128, device=q.device)
    o, _ = chunk_kda(
        q,
        q.clone(),
        v,
        g,
        beta,
        scale=1.0,
        use_qk_l2norm_in_kernel=True,
        use_gate_in_kernel=True,
        use_beta_sigmoid_in_kernel=True,
        safe_gate=True,
        lower_bound=-0.5,
        A_log=param,
        dt_bias=bias,
    )
    assert type(o.grad_fn).__name__ == "ChunkKDAFunctionBackward"
    (db,) = torch.autograd.grad(o[0, 0, 0, 0], beta)
    e = math.exp(-logit)
    exact_approx = (2**30 / (1 + 1e-6)) * e / (1 + e) ** 2
    return dict(
        logit=logit,
        gradient=db.item(),
        real_gradient_as_float64=exact_approx,
        rounded_reference=torch.tensor(exact_approx, dtype=q.dtype).item(),
    )


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--ptx", type=Path, help="save the backward specialization used by this call")
    args = cli.parse_args()
    env = environment()
    probe, control = run(20.0), run(0.0)
    print(json.dumps(dict(**env, probe=probe, control=control), indent=2))
    assert probe["gradient"] == 0 and probe["real_gradient_as_float64"] > 2
    assert control["gradient"] == control["rounded_reference"]
    if args.ptx:
        cache = fused_beta_sigmoid_bwd_kernel.device_caches[torch.cuda.current_device()][0]
        if len(cache) != 1:
            raise ValueError(
                f"Expected one launched sigmoid backward specialization, found {len(cache)}"
            )
        raw = next(iter(cache.values())).asm["ptx"]
        # Publish executable PTX without compiler source locations and trailing DWARF sections.
        # Keep labels and comments in the function, including the final closing brace.
        end = raw.index("\n}", raw.index(".visible .entry")) + 2
        if ".entry" in raw[end:]:
            raise ValueError("unexpected second entry in backward specialization")
        body = [
            line.rstrip() for line in raw[:end].splitlines() if not line.lstrip().startswith(".loc")
        ]
        args.ptx.write_text("\n".join(body) + "\n")
