"""Capture all floating-point words of a dense multi-head call for the independent Lean checker."""

import argparse
import gzip
import hashlib
import json
import struct
from pathlib import Path

import flash_kda
import torch


def raw(tensor):
    width = tensor.element_size() * 8
    dtype = {16: torch.int16, 32: torch.int32}[width]
    return (tensor.detach().contiguous().view(dtype).to(torch.int64) & ((1 << width) - 1)).cpu()


def double_word(value):
    return int.from_bytes(struct.pack("<d", value), "little")


def digest(tensors):
    h = hashlib.sha256()
    for tensor in tensors:
        h.update(tensor.contiguous().view(torch.uint8).cpu().numpy().tobytes())
    return h.hexdigest()


def inputs(lengths, heads=2):
    seq = torch.repeat_interleave(torch.arange(len(lengths)), torch.tensor(lengths))
    t = torch.arange(sum(lengths))[:, None, None]
    j = torch.arange(128)[None, None, :]
    h = torch.arange(heads)[None, :, None]
    s = seq[:, None, None]
    q = ((7 * t + 11 * j + 3 * h + s) % 29 - 14) / 16
    k = ((3 * t + 5 * j + 11 * h + 2 * s) % 31 - 15) / 16
    gate = ((5 * t + 9 * j + 7 * h + 3 * s) % 23 - 11) / 8
    value = ((7 * t + 3 * (j % 4) + 5 * h + s) % 27 - 13) / 16
    beta = (((3 * t + h + s) % 17 - 8) / 8).squeeze(-1)
    q, k, value, gate, beta = [
        v.unsqueeze(0).to("cuda", torch.bfloat16) for v in (q, k, value, gate, beta)
    ]
    param = torch.tensor([-0.375, 0.5], device="cuda")
    bias = (((j[0] + 3 * h[0]) % 19 - 9) / 32).to("cuda")
    b = torch.arange(len(lengths))[:, None, None, None]
    head = torch.arange(heads)[None, :, None, None]
    v = torch.arange(128)[None, None, :, None] % 4
    channel = torch.arange(128)[None, None, None, :]
    initial = (((7 * channel + 11 * v + 5 * head + b) % 23 - 11) / 32).to("cuda")
    return q, k, value, gate, beta, param, bias, initial


def launch(tensors, scale, lower, offsets=None):
    q, k, value, gate, beta, param, bias, initial = tensors
    out, final = torch.full_like(q, torch.nan), torch.full_like(initial, torch.nan)
    flash_kda.fwd(
        q,
        k,
        value,
        gate,
        beta,
        scale,
        out,
        param,
        bias,
        lower,
        initial_state=initial,
        final_state=final,
        cu_seqlens=offsets,
    )
    assert out.isfinite().all() and final.isfinite().all()
    return out, final


def row_classes(initial, value, out, final):
    # A class shares all input AND observed words. A difference in either creates a new class.
    grouped = {}
    for channel in range(value.shape[1]):
        record = tuple(
            tuple(x.tolist())
            for x in (
                initial[channel],
                value[:, channel],
                out[:, channel],
                final[channel],
            )
        )
        grouped.setdefault(record, []).append(channel)
    return [
        dict(members=members, initial=list(i), values=list(v), outputs=list(o), finalState=list(f))
        for (i, v, o, f), members in grouped.items()
    ]


def capture():
    lengths = [1, 17]
    scale, lower = 128**-0.5, -2.25
    tensors = inputs(lengths)
    offsets = torch.tensor([0, 1, 18], dtype=torch.int64, device="cuda")
    out, final = launch(tensors, scale, lower, offsets)
    q, k, value, gate, beta, param, bias, initial = tensors
    cases = []
    for seq, (begin, end) in enumerate(zip(offsets.tolist()[:-1], offsets.tolist()[1:])):
        section = tuple(x[:, begin:end].contiguous() for x in (q, k, value, gate, beta))
        fixed, last = launch((*section, param, bias, initial[seq : seq + 1]), scale, lower)
        for mode, observed, state in [
            ("packed", out[:, begin:end], final[seq]),
            ("fixed", fixed, last[0]),
        ]:
            for h in range(q.shape[2]):
                ra, rb, rv, rg, rl = (raw(x[0, :, h]) for x in section)
                classes = row_classes(
                    raw(initial[seq, h]), rv, raw(observed[0, :, h]), raw(state[h])
                )
                cases.append(
                    dict(
                        label=f"{mode}/sequence-{seq}/head-{h}",
                        scale64=double_word(scale),
                        scale32=int.from_bytes(struct.pack("<f", scale), "little"),
                        lower64=double_word(lower),
                        parameter32=raw(param[h]).item(),
                        bias32=raw(bias[h]).tolist(),
                        stateBits=32,
                        tokens=[
                            dict(q=a.tolist(), k=b.tolist(), gate=g.tolist(), logit=logit.item())
                            for a, b, g, logit in zip(ra, rb, rg, rl, strict=True)
                        ],
                        rows=classes,
                    )
                )
    return dict(
        device=torch.cuda.get_device_name(),
        inputHash=digest((*tensors, offsets)),
        packedOutputHash=digest((out, final)),
        cases=cases,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="destination for the gzipped raw-word capture")
    args = parser.parse_args()
    with torch.inference_mode():
        capture_data = capture()
    data = json.dumps(capture_data, separators=(",", ":")).encode()
    args.output.write_bytes(gzip.compress(data, mtime=0))
    print(
        f"{len(capture_data['cases'])} sequence/head/mode records, SHA-256 {hashlib.sha256(data).hexdigest()}"
    )
