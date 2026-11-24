"""Measure how one gate coordinate changes the output for an exactly orthogonal unit input."""

import argparse
import json
import re
import subprocess
import sys
import tempfile
import warnings
from pathlib import Path

import torch
import flash_kda

ROOT = Path(__file__).resolve().parents[1]
SCALE = 128**-0.5


def inputs(changed):
    q, k, v, g = [
        torch.zeros((1, 1, 1, 128), dtype=torch.bfloat16, device="cuda") for _ in range(4)
    ]
    q[..., :4] = k[..., :4] = 0.5
    k[..., 2:4] = -0.5
    v.fill_(1)
    g[..., 0] = -0.5 if changed else 0
    beta = torch.zeros(q.shape[:-1], dtype=q.dtype, device="cuda")
    param = torch.zeros(1, device="cuda")
    bias = torch.zeros((1, 128), device="cuda")
    return q, k, v, g, beta, param, bias


def word(x):
    return hex(x.view(torch.int16).item() & 0xFFFF)


def public(tensors, offsets, state=None, entry=flash_kda.fwd):
    q, k, v, g, beta, param, bias = tensors
    out = torch.full_like(q, -7)
    entry(q, k, v, g, beta, SCALE, out, param, bias, -5.0, cu_seqlens=offsets, final_state=state)
    assert torch.equal(out.flatten(), out.flatten()[0].expand(128))
    return out


def check_upstream_threshold(gold, output, packed, changed):
    from fla.utils import FLA_CI_ENV, assert_close

    should_reject = changed and not FLA_CI_ENV
    with warnings.catch_warnings(record=True) as captured:
        warnings.simplefilter("always", UserWarning)
        try:
            assert_close("orthogonal gate", gold, output, 0.006 if packed else 0.005)
        except AssertionError as error:
            if not should_reject or "orthogonal gate diff:" not in str(error):
                raise
        else:
            assert not should_reject
    reported = [item for item in captured if "orthogonal gate diff:" in str(item.message)]
    assert bool(reported) == (changed and FLA_CI_ENV)


def cases(packed):
    from fla.utils import get_abs_err, get_err_ratio
    from test_fwd import run_fla_gold_reference
    from torch_ref import torch_ref

    offsets = torch.tensor([0, 1], device="cuda", dtype=torch.int64) if packed else None
    result = []
    for changed in (False, True):
        tensors = inputs(changed)
        q, k, v, g, beta, param, bias = tensors
        baseline = public(tensors, offsets)
        state = torch.full((1, 1, 128, 128), -7.0, device="cuda", dtype=torch.float32)
        assert torch.equal(public(tensors, offsets, state), baseline)
        mixed = public(tensors, offsets, entry=torch_ref)
        gold, _, _, _ = run_fla_gold_reference(
            q, k, v, g, beta, torch.zeros_like(state), param, bias, SCALE, -5.0, offsets
        )
        assert torch.equal(baseline, mixed)
        assert gold.isfinite().all() and gold.abs().max().item() < 1e-9 and state.isfinite().all()
        levels, counts = gold.unique(return_counts=True)
        assert (baseline.count_nonzero().item() == 128) == changed
        assert torch.equal(state, state[:, :, :1, :].expand_as(state))
        assert state[..., 4:].count_nonzero().item() == 0
        ratio = get_err_ratio(gold, baseline.float())
        absolute = get_abs_err(gold, baseline.float())
        check_upstream_threshold(gold, baseline.float(), packed, changed)
        if changed:
            assert ratio > 4000 and 1e-6 < absolute < 0.3
        result.append(
            dict(
                gate_word=word(g.flatten()[0]),
                output_word=word(baseline.flatten()[0]),
                mixed_word=word(mixed.flatten()[0]),
                recurrent_levels=dict(zip(levels.tolist(), counts.tolist(), strict=True)),
                final_state_row_start=state[0, 0, 0, :4].tolist(),
                maximum_absolute_error=absolute,
                reference_ratio=ratio,
            )
        )
    return result


def trace(changed, packed=False):
    entries = json.loads((ROOT / "manifest.json").read_text())["ptx"]["entries"]
    entry = entries[1 if packed else 9]["entry_name"]
    if packed:
        sites = [0x3150, 0x3180, 0x31C0, 0x3200, 0x3230, 0x3280, 0x32C0, 0x3300]
        narrow = 0x3320
    else:
        sites = [0x3220, 0x3250, 0x3290, 0x32D0, 0x3310, 0x3350, 0x3390, 0x33D0]
        narrow = 0x33F0
    script = f"""
set pagination off
set confirm off
set breakpoint pending on
set cuda api_failures hide
set print thread-events off
break fwd_kernel1.cuh:358 if threadIdx.x == 0 && blockIdx.x == 0
run
python
import gdb, json, re
def pc():
    m = re.search(r"<([^<>]+)\\+(\\d+)>:",gdb.execute("x/i $pc",to_string=True))
    if not m or m[1] != {entry!r}:
        raise RuntimeError("unexpected device entry")
    return int(m[2])
def words(offset,width,n):
    buf = gdb.parse_and_eval(f"*(unsigned char @shared (*)[{{width*n}}])($UR4+{{offset}})").bytes
    return [int.from_bytes(buf[i:i+width],"little") for i in range(0,len(buf),width)]
record = dict(cumulative=words(8192,4,4),query_root=words(16384,4,1)[0],key_root=words(16512,4,1)[0])
def stop_at(offset):
    delta = offset - pc()
    gdb.execute(f"tbreak *($pc+{{delta}}) if threadIdx.x == 32 && blockIdx.x == 0", to_string=True)
    gdb.execute("continue", to_string=True)
    assert pc() == offset
def register(number):
    return int(gdb.parse_and_eval("$R"+str(number))) & 0xffffffff
def focus(lane):
    gdb.execute(f"cuda thread ({{32+lane}},0,0)",to_string=True)
gdb.execute("disable breakpoints")
record["accumulation"] = []
last_reg = None
for step, offset in enumerate({sites!r}):
    stop_at(offset)
    line = gdb.execute("x/i $pc",to_string=True)
    match = re.search(r"HMMA\\.16816\\.F32\\.BF16 +R(\\d+), *R(\\d+)(?:\\.reuse)?, *R(\\d+), *R(\\d+|Z)",line)
    if not match:
        raise RuntimeError(line)
    dst, ar, br = map(int,match.group(1,2,3))
    assert match[4] == ("Z" if last_reg is None else str(last_reg))
    before = 0 if last_reg is None else register(last_reg)
    last_reg = dst
    nonzero = []
    for lane in range(4):
        focus(lane)
        for half in range(2):
            aw = register(ar+2*half)
            bw = register(br+half)
            for component in range(2):
                q = (aw >> (16*component)) & 0xffff
                k = (bw >> (16*component)) & 0xffff
                col = step*16+half*8+lane*2+component
                if (q | k) & 0x7fff:
                    nonzero.append([col,q,k])
    focus(0)
    gdb.execute("stepi",to_string=True)
    record["accumulation"].append(dict(pc=offset,before=before,after=register(dst),pairs=nonzero))
stop_at({narrow})
line = gdb.execute("x/i $pc",to_string=True)
regs = re.search(r"F2FP\\.BF16\\.F32\\.PACK_AB +R(\\d+), *R\\d+, *R(\\d+)",line)
assert regs and int(regs[2]) == last_reg, line
dot_reg = int(regs[1])
for name, offset in [("decayed_query",4096),("inverse_key",8192)]:
    tile = words(offset,2,2048)
    assert sum(bool(w & 0x7fff) for w in tile) == 4
    record[name] = tile[:4]
record["accumulator"] = register(last_reg)
end
stepi
python
assert pc() == {narrow + 16}
record["rounded_dot"] = register(dot_reg) & 0xffff
print("GATE_TRACE "+json.dumps(record))
end
continue
"""
    with tempfile.TemporaryDirectory() as temp:
        commands = Path(temp) / "gate.gdb"
        commands.write_text(script)
        p = subprocess.run(
            [
                "cuda-gdb",
                "-batch",
                "-x",
                str(commands),
                "--args",
                sys.executable,
                __file__,
                "--inferior",
                str(int(changed)),
                *(["--packed"] if packed else []),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=150,
        )
    a = re.search(r"^GATE_TRACE (.+)$", p.stdout, re.M)
    b = re.search(r"^PUBLIC_WORD (\w+)$", p.stdout, re.M)
    if p.returncode or not a or not b:
        raise RuntimeError(p.stdout[-8000:])
    record = json.loads(a[1])
    record["output_word"] = int(b[1], 16)
    steps = record["accumulation"]
    assert sorted(steps[0]["pairs"]) == [
        [i, q, k] for i, (q, k) in enumerate(zip(record["decayed_query"], record["inverse_key"]))
    ]
    assert steps[0]["before"] == 0 and steps[0]["after"] == record["accumulator"]
    assert all(
        not step["pairs"] and step["before"] == step["after"] == record["accumulator"]
        for step in steps[1:]
    )
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packed", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--inferior", type=int, choices=(0, 1))
    parser.add_argument(
        "--trace", action="store_true", help="collect device registers in both modes"
    )
    args = parser.parse_args()
    with torch.inference_mode():
        if args.inferior is not None:
            offsets = (
                torch.tensor([0, 1], device="cuda", dtype=torch.int64) if args.packed else None
            )
            print("PUBLIC_WORD", word(public(inputs(bool(args.inferior)), offsets).flatten()[0]))
        else:
            fixed, packed = cases(False), cases(True)
            assert fixed == packed
            result = dict(device=torch.cuda.get_device_name(), fixed=fixed, packed=packed)
            if args.trace:
                result["trace"] = [trace(False), trace(True)]
                result["packed_trace"] = [trace(False, True), trace(True, True)]
                for mode in ("trace", "packed_trace"):
                    for sample, row in zip(result[mode], fixed, strict=True):
                        assert sample["output_word"] == int(row["output_word"], 16)
            print(json.dumps(result, indent=2))
