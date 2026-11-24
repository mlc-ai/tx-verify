"""Read register words in the unmodified GB300 public forward call using the NVIDIA debugger."""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ENTRY = json.loads((Path(__file__).resolve().parents[1] / "manifest.json").read_text())["ptx"][
    "entries"
][9]["entry_name"]


def trace():
    script = """
set pagination off
set confirm off
set breakpoint pending on
set print thread-events off
set cuda api_failures hide
break fwd_kernel1.cuh:294 if threadIdx.x == 0
run
python
import gdb, json, re
record = {}
def snapshot(offset, name, regs=("$R8", "$R10")):
    s = gdb.execute("x/i $pc", to_string=True)
    match = re.search(r"<([^<>]+)\\+(\\d+)>:", s)
    if not match or match[1] != NAME or int(match[2]) != offset:
        raise RuntimeError("unexpected kernel or instruction: " + s)
    record[name] = [hex(int(gdb.parse_and_eval(r)) & 0xffffffff) for r in regs]
snapshot(0xe80, "squared_norms")
end
stepi 2
python snapshot(0xea0, "root_arguments")
stepi 4
python snapshot(0xee0, "inverse_norms")
disable breakpoints
tbreak *($pc + 0x33f0 - 0xee0) if threadIdx.x == 32
continue
python snapshot(0x33f0, "dot_accumulators", ("$R12", "$R13"))
stepi
python snapshot(0x3400, "packed_dots", ("$R12",))
python print("REGISTER_RECORD " + json.dumps(record))
continue
"""
    script = script.replace(" != NAME", f" != {ENTRY!r}")
    with tempfile.TemporaryDirectory() as temp:
        commands = Path(temp) / "registers.gdb"
        commands.write_text(script)
        probe = subprocess.run(
            [
                "cuda-gdb",
                "-batch",
                "-x",
                str(commands),
                "--args",
                sys.executable,
                __file__,
                "--inferior",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=120,
        )
    registers = re.search(r"^REGISTER_RECORD (.+)$", probe.stdout, flags=re.M)
    output = re.search(r"^PUBLIC_RECORD (.+)$", probe.stdout, flags=re.M)
    if probe.returncode or not registers or not output:
        raise RuntimeError(probe.stdout[-9000:])
    result = {**json.loads(registers[1]), **json.loads(output[1])}
    if result["squared_norms"] != ["0x40401000", "0x3f604000"]:
        raise ValueError(f"unexpected square sums: {result}")
    if (
        result["root_arguments"] != ["0x40401004", "0x3f604011"]
        or result["output_word"] != "0x398a"
    ):
        raise ValueError(f"unexpected root arguments or output: {result}")
    if result["dot_accumulators"] != ["0x3a099800", "0x0"] or result["packed_dots"] != ["0x3a0a"]:
        raise ValueError(f"unexpected tensor-core accumulator or rounded product: {result}")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inferior", action="store_true", help=argparse.SUPPRESS)
    if parser.parse_args().inferior:
        import torch

        from one_token import run

        case = run(1 / 32, 1.0)
        result = dict(device=torch.cuda.get_device_name(), output_word=case["output_word"])
        print("PUBLIC_RECORD", json.dumps(result), flush=True)
    else:
        print(json.dumps(trace(), indent=2))
