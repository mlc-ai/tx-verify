"""Read the first gate in the GB300 production binary before and after it becomes nonfinite."""

import argparse
import json
import subprocess
import sys
import tempfile
from pathlib import Path

PARAMETERS = [0, 0x42C80000, 0x7F317217, 0x7F317218]
ROOT = Path(__file__).resolve().parents[1]


def launch(packed):
    import flash_kda
    import torch
    from finite_inputs import words

    shape = (1, 16, 1, 128)
    query, key, value, gate = [
        torch.zeros(shape, device="cuda", dtype=torch.bfloat16) for _ in range(4)
    ]
    strength = torch.zeros(shape[:-1], device="cuda", dtype=torch.bfloat16)
    bias = torch.zeros((1, 128), device="cuda")
    initial = torch.zeros((1, 1, 128, 128), device="cuda")
    offsets = torch.tensor([0, 16], dtype=torch.int64, device="cuda") if packed else None
    results = []
    for word in PARAMETERS:
        parameter = torch.tensor([word], device="cuda", dtype=torch.int32).view(torch.float32)
        out, state = torch.full_like(query, -7), torch.full_like(initial, -7)
        flash_kda.fwd(
            query,
            key,
            value,
            gate,
            strength,
            1.0,
            out,
            parameter,
            bias,
            -5.0,
            initial_state=initial,
            final_state=state,
            cu_seqlens=offsets,
        )
        record = dict(parameter=hex(word), outputs=words(out), final_state=words(state))
        assert record["outputs"] == (["0x7fff"] if word else ["0x0"])
        assert record["final_state"] == (["0x7fffffff"] if word else ["0x0"])
        results.append(record)
    return results


def trace(packed):
    entries = json.loads((ROOT / "manifest.json").read_text())["ptx"]["entries"]
    name = entries[1 if packed else 9]["entry_name"]
    if packed:
        pcs = [0xD70, 0xDA0, 0xF40, 0xF50, 0xFA0]
        source, final, address = "R16", "R2", "R5"
    else:
        pcs = [0xF10, 0xF60, 0x1060, 0x1070, 0x10C0]
        source, final, address = "R15", "R0", "R9"

    script = f"""
set pagination off
set width 0
set confirm off
set breakpoint pending on
set cuda api_failures hide
set print thread-events off
break fwd_kernel1.cuh:172 if threadIdx.x == 0 && blockIdx.x == 0
run
python
import gdb, json, re
def offset():
    line = gdb.execute("x/i $pc",to_string=True)
    match = re.search(r"<([^<>]+)\\+(\\d+)>:",line)
    if not match or match[1] != {name!r}:
        raise RuntimeError("unexpected kernel " + line)
    return int(match[2]),line
def word(reg):
    return hex(int(gdb.parse_and_eval("$"+reg)) & 0xffffffff)
def stop(pc, opcode):
    current,_ = offset()
    if current < pc:
        gdb.execute(f"tbreak *($pc+{{pc-current}}) if threadIdx.x == 0 && blockIdx.x == 0",
                    to_string=True)
        gdb.execute("continue",to_string=True)
    actual,line = offset()
    if actual != pc or opcode not in line:
        raise RuntimeError("unexpected instruction " + line)
registers = []
for index, expected in enumerate({PARAMETERS!r}):
    if index:
        gdb.execute("enable 1",to_string=True)
        gdb.execute("continue",to_string=True)
    gdb.execute("disable 1",to_string=True)
    stop({pcs[0]},"FMUL.FTZ")
    record = dict(parameter=word({source!r}))
    assert record["parameter"] == hex(expected)
    stop({pcs[1]},"MUFU.EX2")
    record["exponent_input"] = word("R4")
    stop({pcs[2]},"FMUL.FTZ")
    record.update(exponential=word("R4"), biased_gate=word("R7"))
    stop({pcs[3]},"FMUL.FTZ")
    record["product"] = word("R7")
    stop({pcs[4]},"STS")
    record["first_gate_prefix"] = word({final!r})
    record["gate_scale"] = word("UR5")
    gdb.execute("stepi",to_string=True)
    shared = gdb.parse_and_eval("*(unsigned int @shared *)(" + "$" + {address!r} + "+0x2000)")
    record["shared_gate_prefix"] = hex(int(shared) & 0xffffffff)
    registers.append(record)
with open(REGISTER_PATH,"w") as target:
    json.dump(registers,target)
end
continue
"""
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "gate.gdb"
        captures = Path(folder) / "registers.json"
        outputs = Path(folder) / "outputs.json"
        path.write_text(script.replace("REGISTER_PATH", repr(str(captures))))
        cmd = [
            "cuda-gdb",
            "-batch",
            "-x",
            str(path),
            "--args",
            sys.executable,
            __file__,
            "--inferior",
            str(outputs),
        ]
        if packed:
            cmd.append("--packed")
        run = subprocess.run(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=180
        )
        if run.returncode or not captures.exists() or not outputs.exists():
            raise RuntimeError(run.stdout[-7000:])
        registers = json.loads(captures.read_text())
        public = json.loads(outputs.read_text())
    assert len(registers) == len(PARAMETERS)
    for index, (intermediate, result) in enumerate(zip(registers, public, strict=True)):
        assert intermediate["parameter"] == result["parameter"] == hex(PARAMETERS[index])
        assert intermediate["biased_gate"] == "0x0"
        assert (
            intermediate["exponent_input"]
            == ["0x0", "0x431044fe", "0x7f7ffffe", "0x7f800000"][index]
        )
        assert intermediate["exponential"] == ("0x7f800000" if index else "0x3f800000")
        assert intermediate["gate_scale"] == "0xc0e6d4ca"
        assert intermediate["shared_gate_prefix"] == intermediate["first_gate_prefix"]
        assert intermediate["product"] == ("0x7fffffff" if index else "0x0")
        assert intermediate["first_gate_prefix"] == ("0x7fffffff" if index else "0xc066d4ca")
    return [{**a, **b} for a, b in zip(registers, public, strict=True)]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inferior", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--packed", action="store_true")
    args = parser.parse_args()
    if args.inferior:
        args.inferior.write_text(json.dumps(launch(args.packed)))
    else:
        print(json.dumps(trace(args.packed), indent=2))
