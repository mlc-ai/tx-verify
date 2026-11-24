# SPDX-License-Identifier: Apache-2.0
"""Compare FLA's KDA backward on GB300 with autograd through an independent float64 recurrence."""

import json


import torch
from fla.ops.kda import chunk_kda
from provenance import environment

NAMES = ("query", "key", "value", "gate", "strength_logit", "log_parameter", "bias", "initial")
DIM = 128
SCALE = DIM**-0.5
LOWER = -0.5


def exact(args, lengths):
    q, k, v, gate, logits, param, bias, initial = args
    q, k = (x / (x.square().sum(-1, keepdim=True) + 1e-6).sqrt() for x in (q, k))
    log_decay = LOWER * torch.sigmoid(param.exp()[:, None] * (gate + bias.reshape(-1, DIM)))
    outputs, final = [], []
    start = 0
    for seq, length in enumerate(lengths):
        # The upstream test uses state buffers with value before key.
        state = initial[seq].transpose(-1, -2)
        for t in range(start, start + length):
            before = state * log_decay[0, t].exp().unsqueeze(-1)
            key = k[0, t].unsqueeze(-1)
            residual = v[0, t] - (before * key).sum(-2)
            state = before + key * (logits[0, t].sigmoid().unsqueeze(-1) * residual).unsqueeze(-2)
            outputs.append(SCALE * (q[0, t].unsqueeze(-1) * state).sum(-2))
        final.append(state.transpose(-1, -2))
        start += length
    return torch.stack(outputs).unsqueeze(0), torch.stack(final)


def fused(args, lengths):
    q, k, v, gate, logits, param, bias, initial = args
    offsets = None
    if len(lengths) > 1:
        offsets = torch.tensor([0, *lengths], dtype=torch.long, device=q.device).cumsum(0)
    return chunk_kda(
        q=q,
        k=k,
        v=v,
        g=gate,
        beta=logits,
        use_beta_sigmoid_in_kernel=True,
        scale=SCALE,
        initial_state=initial,
        output_final_state=True,
        use_qk_l2norm_in_kernel=True,
        use_gate_in_kernel=True,
        safe_gate=True,
        lower_bound=LOWER,
        A_log=param,
        dt_bias=bias,
        cu_seqlens=offsets,
        state_v_first=True,
    )


def compare(lengths, seed, seed_outputs, seed_final):
    rng = torch.Generator().manual_seed(seed)

    def sample(shape, dtype, scale=1.0):
        return (torch.randn(shape, generator=rng) * scale).to(dtype).cuda()

    bf, fp = torch.bfloat16, torch.float32
    shape = (1, sum(lengths), 2, DIM)
    args = [sample(shape, bf) for _ in range(4)] + [
        sample(shape[:-1], bf),
        sample((2,), fp, 0.2),
        sample((2 * DIM,), fp, 0.2),
        sample((len(lengths), 2, DIM, DIM), fp, 0.1),
    ]
    seeds = [sample(shape, bf) * seed_outputs, sample(args[-1].shape, fp) * seed_final]
    refs = [x.double().requires_grad_() for x in args]
    actual = [x.requires_grad_() for x in args]
    ref_grad = torch.autograd.grad(exact(refs, lengths), refs, [x.double() for x in seeds])
    o, h = fused(actual, lengths)
    assert type(o.grad_fn).__name__ == "ChunkKDAFunctionBackward"
    gpu_grad = torch.autograd.grad((o, h), actual, seeds)
    metrics = {}
    for name, got, ref in zip(NAMES, gpu_grad, ref_grad, strict=True):
        assert torch.isfinite(got).all() and torch.isfinite(ref).all(), name
        delta = got.double() - ref
        norm = ref.norm().item()
        if norm == 0:
            assert torch.count_nonzero(delta) == 0, name
        metrics[name] = dict(
            relative_l2=delta.norm().item() / norm if norm else 0.0,
            max_abs=delta.abs().max().item(),
        )
    return dict(
        lengths=lengths,
        seed=seed,
        output_weight=seed_outputs,
        final_weight=seed_final,
        gradients=metrics,
    )


if __name__ == "__main__":
    env = environment()
    cases = [
        compare(lengths, seed, out, final)
        for lengths, seed, out, final in (
            ([1], 41, 1, 0),
            ([17], 42, 0, 1),
            ([65], 43, 1, 1),
            ([17, 65], 44, 1, 1),
        )
    ]
    print(json.dumps(dict(**env, cases=cases), indent=2))
    assert all(m["relative_l2"] < 0.05 for c in cases for m in c["gradients"].values())
