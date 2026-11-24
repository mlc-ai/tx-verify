"""Check both public input tensor maps and every shared query/key byte on a GB300."""

import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# The packed input has two sequences of lengths 1 and 16.
CASES = {"fixed_tail": (9, 1, 16), "packed_first": (1, 0, 0), "packed_second": (1, 1, 1)}
ROOT = Path(__file__).resolve().parents[1]


def launch(case, folder):
    import torch

    import flash_kda

    shape = (1, 17, 2, 128)
    words = torch.arange(17 * 2 * 128, device="cuda", dtype=torch.int16).reshape(shape)
    q, k = [(words + start).view(torch.bfloat16) for start in (0x3000, -0x5000)]
    # Copy the actual public buffers to the host before launching. Select head one.
    first = CASES[case][2]
    for name, tensor in (("query", q), ("key", k)):
        rows = (
            tensor[0, first : first + 16, 1].contiguous().view(torch.uint8).cpu().numpy().tobytes()
        )
        (folder / name).write_bytes(rows.ljust(4096, b"\0"))
    offsets = (
        torch.tensor([0, 1, 17], device="cuda", dtype=torch.int64)
        if case.startswith("packed")
        else None
    )
    print(
        "PUBLIC", json.dumps([q.data_ptr(), k.data_ptr(), torch.cuda.get_device_name()]), flush=True
    )
    flash_kda.fwd(
        q,
        k,
        torch.zeros_like(q),
        torch.zeros_like(q),
        torch.zeros_like(q[..., 0]).contiguous(),
        1.0,
        torch.empty_like(q),
        torch.zeros(2, device="cuda"),
        torch.zeros((2, 128), device="cuda"),
        0.0,
        cu_seqlens=offsets,
    )
    torch.cuda.synchronize()


def trace(case):
    entry_index, block, first = CASES[case]
    entry = json.loads((ROOT / "manifest.json").read_text())["ptx"]["entries"][entry_index][
        "entry_name"
    ]
    # CUDA-GDB stops one instruction into the driver's AArch64 prologue. The caller's
    # stack pointer addresses the four enumerated stack arguments at the ABI boundary.
    commands = """
set pagination off
set confirm off
set breakpoint pending on
set print thread-events off
set cuda api_failures hide
break cuTensorMapEncodeTiled
commands
silent
python
import gdb, json
reg = lambda name: int(gdb.parse_and_eval("$" + name))
def read(address, size):
    return int.from_bytes(bytes(gdb.selected_inferior().read_memory(address, size)), "little")
def array(register, width, count):
    return [read(reg(register) + n*width, width) for n in range(count)]
rank = reg("x2")
stack = int(gdb.newest_frame().older().read_register("sp"))
print("ENCODE", json.dumps([reg("x3"), reg("x1"), array("x4", 8, rank), array("x5", 8, rank-1),
    array("x6", 4, rank), array("x7", 4, rank), [read(stack + n*8, 4) for n in range(4)]]))
end
continue
end
break fwd_kernel1.cuh:294 if threadIdx.x == 0 && blockIdx.y == 1 && blockIdx.x == BLOCK
run
python
if "<" + ENTRY + "+" not in gdb.execute("x/i $pc", to_string=True):
    raise RuntimeError("unexpected device kernel")
tile = gdb.parse_and_eval("*(unsigned short @shared (*)[4096])$UR4")
with open(DEST, "wb") as out:
    out.write(tile.bytes)
end
disable breakpoints
continue
"""
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        script = commands.replace("== BLOCK", f"== {block}").replace(
            " + ENTRY + ", f" + {entry!r} + "
        )
        (folder / "trace.gdb").write_text(
            script.replace("open(DEST,", f"open({str(folder / 'shared')!r},")
        )
        result = subprocess.run(
            [
                "cuda-gdb",
                "-batch",
                "-x",
                str(folder / "trace.gdb"),
                "--args",
                sys.executable,
                __file__,
                "--launch",
                case,
                str(folder),
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=150,
        )
        if result.returncode or not (folder / "shared").is_file():
            raise RuntimeError(result.stdout[-5000:])
        q, k, device = json.loads(re.search(r"^PUBLIC (.+)$", result.stdout, re.M)[1])
        raw_maps = [json.loads(m) for m in re.findall(r"^ENCODE (.+)$", result.stdout, re.M)]
        expected_map = [9, [128, 17, 2], [512, 256], [128, 16, 1], [1, 1, 1], [0, 0, 2, 0]]
        for pointer in (q, k):
            if [fields for ptr, *fields in raw_maps if ptr == pointer] != [expected_map]:
                raise ValueError("tensor map differs from expected public descriptor")
        data = (folder / "shared").read_bytes()
        if data != (folder / "query").read_bytes() + (folder / "key").read_bytes():
            raise ValueError(f"{case}: shared tile differs from the public query/key bytes")
    return dict(
        case=case,
        device=device,
        first_token=first,
        head=1,
        bytes_compared=len(data),
        shared_sha256=hashlib.sha256(data).hexdigest(),
        driver_arguments=expected_map,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--launch", choices=CASES)
    parser.add_argument("folder", nargs="?", type=Path)
    args = parser.parse_args()
    if args.launch:
        launch(args.launch, args.folder)
    else:
        if platform.machine() != "aarch64":
            raise RuntimeError("The host register reader requires the AArch64 calling convention.")
        print(json.dumps([trace(case) for case in CASES], indent=2))
