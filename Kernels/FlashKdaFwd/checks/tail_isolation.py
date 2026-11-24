"""Compare one sequence before and after changing one key word in the following sequence."""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

import torch

import flash_kda
import flash_kda_C

WORDS = {"zero": 0, "largest_finite": 0x7F7F, "quiet_nan": 0x7FC1}
ROOT = Path(__file__).resolve().parents[1]


def inputs(mode, length):
    shape = (2, length, 1, 128) if mode == "fixed" else (1, length + 1, 1, 128)
    q, k, v, g = [torch.zeros(shape, device="cuda", dtype=torch.bfloat16) for _ in range(4)]
    q[..., 0] = k[..., 0] = v[..., 0] = 1
    beta = torch.zeros(shape[:-1], device="cuda", dtype=torch.bfloat16)
    offsets = None
    if mode == "packed":
        offsets = torch.tensor([0, length, length + 1], device="cuda", dtype=torch.int64)
    return q, k, v, g, beta, offsets


def forward(tensors, record_state=True, workspace=None):
    q, k, v, g, beta, offsets = tensors
    state = (
        torch.full((2, 1, 128, 128), -7.0, device="cuda", dtype=torch.float32)
        if record_state
        else None
    )
    out = torch.full_like(q, -7)
    args = (q, k, v, g, beta, 1.0, out)
    gate = (torch.zeros(1, device="cuda"), torch.zeros((1, 128), device="cuda"), 0.0)
    if workspace is None:
        flash_kda.fwd(*args, *gate, final_state=state, cu_seqlens=offsets)
    else:
        flash_kda_C.fwd(*args, workspace, *gate, final_state=state, cu_seqlens=offsets)
    return out.reshape(-1, 128), None if state is None else state[0]


def set_word(tensors, length, word):
    tensors[1].view(torch.int16).reshape(-1, 128)[length, 7] = word


def word16(x):
    return f"0x{x.view(torch.int16).item() & 0xFFFF:04x}"


def check(mode):
    minimal = {}
    for length in range(1, 33):
        tensors = inputs(mode, length)
        baseline, state = forward(tensors)
        prefix = baseline[:length]
        assert prefix.isfinite().all() and state.isfinite().all()
        for kind, word in WORDS.items():
            set_word(tensors, length, word)
            out, h = forward(tensors)
            unaffected = length if kind != "quiet_nan" else length // 16 * 16
            assert torch.equal(
                prefix[:unaffected].view(torch.int16), out[:unaffected].view(torch.int16)
            )
            if unaffected == length:
                assert torch.equal(state.view(torch.int32), h.view(torch.int32))
            else:
                assert out[unaffected:length].isnan().all() and h.isnan().all()
            if length == 1:
                default_out, _ = forward(tensors, record_state=False)
                assert torch.equal(default_out[0].view(torch.int16), out[0].view(torch.int16))
                minimal[kind] = dict(
                    default_first_output_word=word16(default_out[0, 0]),
                    following_key_word=hex(word),
                    first_output_word=word16(out[0, 0]),
                    nan_output_count=out[0].isnan().sum().item(),
                    nan_state_count=h.isnan().sum().item(),
                )
    return minimal


def workspace_trace(mode):
    tensors = inputs(mode, 1)
    set_word(tensors, 1, WORDS["quiet_nan"])
    size = flash_kda_C.get_workspace_size(2, 1, 2)
    workspace = torch.full((size,), 0xA5, device="cuda", dtype=torch.uint8)
    out, state = forward(tensors, workspace=workspace)
    # The first 4,096 bytes hold the decayed keys for the first head and first tile.
    keys = workspace[:4096].view(torch.bfloat16).reshape(16, 128)
    assert keys[0].isfinite().all() and word16(keys[0, 0]) == "0x3f80"
    assert keys[1].isnan().all() and (keys[2:] == 0).all()
    assert out[0].isnan().all() and state.isnan().all()
    return dict(
        decayed_key_nan_counts_by_row=keys.isnan().sum(1).tolist(),
        next_row_channel_seven_word=word16(keys[1, 7]),
    )


def shared_trace(mode):
    entry = json.loads((ROOT / "manifest.json").read_text())["ptx"]["entries"][
        9 if mode == "fixed" else 1
    ]["entry_name"]
    with tempfile.TemporaryDirectory() as tmp:
        commands = Path(tmp) / "trace.gdb"
        commands.write_text(f"""
set pagination off
set confirm off
set breakpoint pending on
set print thread-events off
set cuda api_failures hide
break fwd_kernel1.cuh:294 if threadIdx.x == 0 && blockIdx.x == 0
break fwd_kernel1.cuh:358 if threadIdx.x == 0 && blockIdx.x == 0
run
python
import gdb, json
def check_pc():
    if "<" + {entry!r} + "+" not in gdb.execute("x/i $pc", to_string=True):
        raise RuntimeError("unexpected device entry")
def shared(offset, size):
    return gdb.parse_and_eval(f"*(unsigned char @shared (*)[{{size}}])($UR4+{{offset}})").bytes
check_pc()
before = shared(4096,4096)
end
disable 1
continue
python
check_pc()
after = shared(4096,4096)
roots = shared(16512,64)
bits = lambda x: [int.from_bytes(x[i:i+4], "little") for i in range(0,len(x),4)]
emit = lambda name, data: open({tmp!r}+"/"+name,"wb").write(data)
emit("before",before)
emit("after",after)
print("ROOTS",json.dumps(bits(roots)))
end
disable breakpoints
continue
""")
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
                mode,
            ],
            capture_output=True,
            text=True,
            timeout=120,
        )
        root_match = re.search(r"^ROOTS (.+)$", p.stdout, re.M)
        public = re.search(r"^PUBLIC (.+)$", p.stdout, re.M)
        if p.returncode or not root_match or not public:
            raise RuntimeError(p.stdout[-4000:] + p.stderr[-2000:])
        roots = json.loads(root_match[1])
        before, after = [(Path(tmp) / name).read_bytes() for name in ("before", "after")]
    live_row = (0x3F80).to_bytes(2, "little") + bytes(254)
    next_row = bytearray(live_row)
    next_row[14:16] = WORDS["quiet_nan"].to_bytes(2, "little")
    assert before == live_row + next_row + bytes(14 * 256)
    assert after == live_row + bytes(15 * 256)
    assert (roots[1] & 0x7FFFFFFF) > 0x7F800000
    assert all((r & 0x7FFFFFFF) < 0x7F800000 for r in [roots[0], *roots[2:]])
    assert json.loads(public[1]) == "0x7fff"
    return dict(
        key_bytes_checked_at_each_stage=len(after),
        next_key_word_before="0x7fc1",
        next_key_word_after="0x0000",
        valid_row_inverse_length=f"0x{roots[0]:08x}",
        next_row_inverse_length=f"0x{roots[1]:08x}",
        first_output_word="0x7fff",
    )


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--inferior", choices=("fixed", "packed"))
    cli.add_argument("--shared", action="store_true")
    args = cli.parse_args()
    if args.inferior:
        case = inputs(args.inferior, 1)
        set_word(case, 1, WORDS["quiet_nan"])
        output, _ = forward(case)
        print("PUBLIC", json.dumps(word16(output[0, 0])), flush=True)
    else:
        result = dict(
            device=torch.cuda.get_device_name(),
            first_sequence_lengths=list(range(1, 33)),
            second_sequence_lengths={"fixed": "same as first", "packed": 1},
            changed_key_channel=7,
            workspace={mode: workspace_trace(mode) for mode in ("fixed", "packed")},
            cases={mode: check(mode) for mode in ("fixed", "packed")},
        )
        if args.shared:
            result["shared"] = {mode: shared_trace(mode) for mode in ("fixed", "packed")}
        print(json.dumps(result, indent=2))
