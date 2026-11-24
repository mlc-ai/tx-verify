"""Trace one fixed-length public launch from its preparation buffers to the last output store."""

import argparse
import json
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = json.loads((HERE.parent / "manifest.json").read_text())
ENTRY = MANIFEST["ptx"]["entries"][12]["entry_name"]
# Byte offsets in the pinned sm_103a machine code. Register lists follow arithmetic operand order.
SITES = [
    (0x7870, 28, "residual_scale", [58, 4]),
    (0x7920, 28, "scaled_residual", [58, 59]),
    (0x7B80, 0, "output_accumulator", [48]),
    (0x7C10, 0, "output_conversion", [48, 49]),
    (0x7C90, 0, "output_shared_store", [4, 48]),
    (0x7D60, 0, "state_fma", [107, 55, 32]),
    (0x7D70, 0, "updated_state", [107]),
    (0x7F50, 0, "state_shared_store", [204, 24]),
    (0x95C0, 160, "before_global_store", [4, 5, 28]),
    (0x95D0, 160, "after_global_store", [4, 5, 28]),
]


def nonzero_halfwords(matrix):
    return [
        [*index, f"{int(matrix[tuple(index)]) & 0xFFFF:04x}"] for index in matrix.nonzero().tolist()
    ]


def source_words(args, gates):
    import torch

    q, k, v, gate, beta, scale = args
    param, bias, bound = gates
    assert q.shape == k.shape == v.shape == gate.shape == (1, 33, 1, 128)
    assert beta.shape == (1, 33, 1)
    result = {}
    for name, tensor in [("q", q), ("k", k), ("v", v), ("logits", beta)]:
        result[name] = nonzero_halfwords(tensor.view(torch.int16).reshape(33, -1))
    uniform = gate.view(torch.int16)[0, :, 0, :]
    assert torch.equal(uniform, uniform[:, :1].expand_as(uniform))
    result["gate"] = [f"{int(w) & 0xFFFF:04x}" for w in uniform[:, 0]]
    assert param.shape == (1,) and bias.shape == (1, 128)
    assert (
        not param.view(torch.int32).count_nonzero() and not bias.view(torch.int32).count_nonzero()
    )
    result["parameter_and_bias"] = "positive zero in all coordinates"
    result["scale"] = struct.pack(">f", scale).hex()
    result["lower_bound"] = struct.pack(">f", bound).hex()
    return result


def workspace_words(ws):
    import torch

    tiles = 3
    pos = 0
    result = {}
    for name, rows, cols in [
        ("decayed_key", 16, 128),
        ("decayed_query", 16, 128),
        ("restored_key", 16, 128),
        ("decay", 1, 128),
        ("inverse", 16, 16),
        ("query_key", 16, 16),
    ]:
        wide = name == "decay"
        size = (4 if wide else 2) * tiles * rows * cols
        matrix = (
            ws[pos : pos + size]
            .view(torch.int32 if wide else torch.int16)
            .reshape(tiles, rows, cols)
        )
        pos += size
        if wide:
            words = matrix[:, 0, 0]
            assert torch.equal(matrix, words[:, None, None].expand_as(matrix))
            result[name] = [f"{int(x) & 0xFFFFFFFF:08x}" for x in words]
        elif name == "inverse":
            identity = torch.eye(16, device=ws.device, dtype=torch.bfloat16).view(torch.int16)
            assert torch.equal(matrix, identity.expand_as(matrix))
            result[name] = "identity in all three blocks"
        else:
            result[name] = nonzero_halfwords(matrix)
    return result


def inferior():
    import torch

    import flash_kda
    from stateless_output import inputs

    args, gates = inputs(2.0**-16, 2.0**-28)
    out = torch.full_like(args[0], -7)
    raw_inputs = source_words(args, gates)
    buffers = []

    def capture(frame, event, _):
        if event == "return" and frame.f_code is flash_kda.fwd.__code__:
            buffers.append(frame.f_locals["workspace"])

    previous = sys.getprofile()
    try:
        sys.setprofile(capture)
        flash_kda.fwd(*args, out, *gates)
    finally:
        sys.setprofile(previous)
    assert out.nonzero().tolist() == [[0, 32, 0, 0]] and len(buffers) == 1
    last = out[0, 32, 0, 0]
    host = dict(
        device=torch.cuda.get_device_name(),
        output_base=out.data_ptr(),
        output_address=last.data_ptr(),
        public_word=last.view(torch.int16).item(),
        inputs=raw_inputs,
        preparation=workspace_words(buffers[0]),
    )
    print("PUBLIC_WINDOW " + json.dumps(host), flush=True)


def trace():
    script = """set pagination off
set confirm off
set breakpoint pending on
set print thread-events off
set cuda api_failures hide
break fwd_kernel2.cuh:606 if threadIdx.x == 28
run
python
import gdb, json, re
def location():
    instruction = gdb.execute('x/i $pc', to_string=True)
    match = re.search(r'<([^<>]+)\\+(\\d+)>:\\s*(.+)', instruction)
    if not match or match[1] != ENTRY_NAME:
        raise RuntimeError('unexpected kernel: ' + instruction)
    return int(match[2]), match[3].strip()
origin, _ = location()
assert origin <= 0x7870, hex(origin)
base = int(gdb.parse_and_eval('$pc')) - origin
def register(i):
    return int(gdb.parse_and_eval('$R' + str(i))) & 0xffffffff
def sample(name, pc, regs):
    offset, instruction = location()
    assert offset == pc
    words = [register(i) for i in regs]
    record = dict(site=name, instruction=instruction, offset=pc, registers=words)
    if name in ('before_global_store','after_global_store'):
        addr = (words[1] << 32) + words[0] - 8
        record['address'] = addr
        memory = gdb.execute('x/1hx ' + hex(addr), to_string=True)
        record['memory'] = int(memory.strip().split()[-1],16)
    print('DEVICE_WINDOW ' + json.dumps(record))
end
disable 1
""".replace("ENTRY_NAME", repr(ENTRY))
    for number, (pc, thread, label, regs) in enumerate(SITES, start=2):
        script += (
            f"python gdb.execute('break *' + hex(base + {pc}) + ' if threadIdx.x == {thread}')\n"
            f"commands {number}\nsilent\npython sample({label!r},{pc},{regs!r})\ncontinue\nend\n"
        )
    with tempfile.TemporaryDirectory() as tmp:
        commands = Path(tmp) / "trace.gdb"
        commands.write_text(script + "continue\n")
        process = subprocess.run(
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
            timeout=150,
        )
    public = re.search(r"^PUBLIC_WINDOW (.+)$", process.stdout, re.M)
    if process.returncode or not public:
        raise RuntimeError(process.stdout[-9000:])
    host = json.loads(public[1])
    target = host.pop("output_address")
    host["output_offset_bytes"] = target - host.pop("output_base")
    assert host["output_offset_bytes"] == 32 * 128 * 2
    by_site = {name: [] for _, _, name, _ in SITES}
    for raw in re.findall(r"^DEVICE_WINDOW (.+)$", process.stdout, re.M):
        row = json.loads(raw)
        site = row.pop("site")
        if "address" in row:
            assert row.pop("address") == target
            row["registers"] = row["registers"][2:]
        by_site[site].append(row)
    for _, _, name, _ in SITES:
        assert len(by_site[name]) == (1 if "global_store" in name else 3), name
    before, after = (by_site[s][0] for s in ("before_global_store", "after_global_store"))
    assert (before["memory"], after["memory"], host["public_word"]) == (0xC0E0, 0x3F81, 0x3F81)
    assert [x["registers"] for x in by_site["state_fma"]] == [
        [0, 0x3F800000, 0x3FC00000],
        [0x3FC00000, 0x3F2CAAAA, 0xA3020000],
        [0x3F817FFF, 0x3F800000, 0],
    ]
    return {**host, "sites": by_site}


def lean_data(record):
    """Emit the observed workspace cells and numerical register operands for the Lean checker."""
    prep = record["preparation"]
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        "-- Generated by checks/stateless_trace.py from a public GB300 launch.",
        "module",
        "",
        "@[expose] public section",
        "namespace FlashKda.Stateless.Observed",
        "",
    ]
    raw = record["inputs"]
    for name in ("q", "k", "v", "logits"):
        cells = ", ".join(f"({t},{i},0x{w})" for t, i, w in raw[name])
        lines.extend([f"def raw{name.title()} : List (Nat × Nat × Nat) :=", f"  [{cells}]"])
    assert raw["parameter_and_bias"] == "positive zero in all coordinates"
    lines.extend(
        [
            "def rawGate : List Nat :=",
            "  ["
            + ",\n   ".join(
                ",".join("0x" + w for w in raw["gate"][i : i + 8])
                for i in range(0, len(raw["gate"]), 8)
            )
            + "]",
            f"def rawScale := 0x{raw['scale']}",
            f"def rawBound := 0x{raw['lower_bound']}",
        ]
    )
    for source, target in [
        ("decayed_key", "decayedKey"),
        ("decayed_query", "decayedQuery"),
        ("restored_key", "restoredKey"),
        ("query_key", "queryKey"),
    ]:
        cells = ", ".join(f"({b},{i},{j},0x{w})" for b, i, j, w in prep[source])
        lines.extend([f"def {target} : List (Nat × Nat × Nat × Nat) :=", f"  [{cells}]"])
    assert prep["inverse"] == "identity in all three blocks"
    lines.append("def decay : List Nat := [" + ",".join("0x" + w for w in prep["decay"]) + "]")
    for _, _, name, _ in SITES:
        values = [row["registers"] for row in record["sites"][name]]
        words = ", ".join("[" + ",".join(hex(w) for w in row) + "]" for row in values)
        target = name.split("_")[0] + "".join(w.title() for w in name.split("_")[1:])
        lines.extend([f"def {target} : List (List Nat) :=", f"  [{words}]"])
    for field, name in [
        ("before_global_store", "initialMemory"),
        ("after_global_store", "finalMemory"),
    ]:
        lines.append(f"def {name} := {hex(record['sites'][field][0]['memory'])}")
    lines.extend(
        [
            f"def outputOffset := {record['output_offset_bytes']}",
            f"def publicWord := {hex(record['public_word'])}",
            "",
            "end FlashKda.Stateless.Observed",
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inferior", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--lean-data", type=Path, help="emit Lean data from a saved JSON trace")
    args = parser.parse_args()
    if args.lean_data:
        print(lean_data(json.loads(args.lean_data.read_text())), end="")
    elif args.inferior:
        inferior()
    else:
        print(json.dumps(trace(), indent=2))
