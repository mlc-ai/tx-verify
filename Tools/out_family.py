# SPDX-License-Identifier: Apache-2.0
"""Instances of a run family's handwritten template, generated from the PTX (`Tools/out_gen.py`).

A family is the set of generated runs (`Tools/out_gen.py`) with the same instruction shape, e.g.
the 32 dequantized chunks of a kernel. Their values and conditions are proved once, as a Lean
TEMPLATE, and this tool writes one copy per instance with the instance's names and register ids
substituted. A family declaration (a `Tools/out_gen.py` declaration with `"template"`):

    {"ptx": "Kernels/K/k.ptx", "namespace": "PTX.Kernels.K.Data.Chunks0",
     "output": "Kernels/K/Data/Chunks0.lean", "imports": ["Kernels.K.Gen.Runs1"],
     "open": ["PTX.Kernels.K"], "template": "Kernels/K/Data/chunk.tmpl",
     "instances": [{"decl": "Kernels/K/Gen/Out/runs1.json", "run": "dr2738",
                    "params": {"name": "chunk00"}}]}

Each instance names a run of a run declaration (its `start`, `end`, `outputs` are read from it).
The template is Lean text whose first line is `-- shape: <opcode> <opcode> …`, the run's
opcodes (checked against every instance), followed by declarations with placeholders `${key}`:

    ${run}            the run's name, prefixed by `prefix` of the instance's declaration if any
    ${start} ${end}   the run's first pc and the pc after it; ${len} the number of instructions
    ${v<k>}           the value def of the run's k-th instruction (`<run>_v<pc>`, from 0)
    ${op<k>}          the decoded instruction def of a Core item (`<run>_op<pc>`)
    ${pc<k>}          the k-th instruction's pc
    ${d<k>}           the register id of its first destination
    ${s<k>_<j>}       the register id of its j-th register source (from 0)
    ${in<j>} ${out<j>} the j-th register of the run's facts at its start / end (the generated
                      `<run>_facts0` / last facts order: ascending ids)
    ${<param>}        an instance parameter

The instances are written in order; the file header, imports, namespace and `open` lines are
generated. No proof is generated: the template's proofs are elaborated per instance, so a
template is written against names, never against literal register ids.
"""

import json
import re
from pathlib import Path

import flow_gen
import parse_ptx
from lean_wrap import wrap_lines

ROOT = Path(__file__).resolve().parents[1]
PLACE = re.compile(r"\$\{(\w+)\}")


class FamilyError(Exception):
    pass


def regs_in(text, ids):
    """Register operands of an operand text, in order (vector and address forms included)."""
    return [x for x in re.findall(r"%[\w$.]+", text) if x in ids]


def shape_of(template):
    first = template.splitlines()[0] if template else ""
    if not first.startswith("-- shape:"):
        raise FamilyError("the template's first line is not `-- shape: <opcodes>`")
    return first[len("-- shape:") :].split(), "\n".join(template.splitlines()[1:])


def live_sets(code, ids, run):
    """Ascending register ids of the facts at the run's start and at its end."""
    start, end = run["start"], run["end"]
    cur = {ids[x] for x in run.get("outputs", [])}
    out = sorted(cur)
    for pc in range(end - 1, start - 1, -1):
        ins = code[pc]
        ops = ins.get("resolved", ins["operands"])
        wr = regs_in(ops[0], ids)
        rd = [r for x in ops[1:] for r in regs_in(x, ids)]
        cur = (cur - {ids[x] for x in wr}) | {ids[x] for x in rd}
    return sorted(cur), out


def keys_of(code, ids, run, prefix):
    name = prefix + run["name"]
    start, end = run["start"], run["end"]
    keys = {"run": name, "start": start, "end": end, "len": end - start}
    for k, pc in enumerate(range(start, end)):
        ins = code[pc]
        ops = ins.get("resolved", ins["operands"])
        keys[f"v{k}"] = f"{name}_v{pc}"
        keys[f"op{k}"] = f"{name}_op{pc}"
        keys[f"pc{k}"] = pc
        wr = regs_in(ops[0], ids)
        if wr:
            keys[f"d{k}"] = ids[wr[0]]
        for j, x in enumerate(r for o in ops[1:] for r in regs_in(o, ids)):
            keys[f"s{k}_{j}"] = ids[x]
    lin, lout = live_sets(code, ids, run)
    keys.update({f"in{j}": r for j, r in enumerate(lin)})
    keys.update({f"out{j}": r for j, r in enumerate(lout)})
    return keys


def instance(template, keys, where):
    def sub(m):
        if m.group(1) not in keys:
            raise FamilyError(f"{where}: no value for ${{{m.group(1)}}}")
        return str(keys[m.group(1)])

    return PLACE.sub(sub, template)


def render(decl, header):
    ptx = ROOT / decl["ptx"]
    program = parse_ptx.parse(ptx.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    shape, body = shape_of((ROOT / decl["template"]).read_text())
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        *header(decl["ptx"]),
        f"-- Template: {decl['template']}",
        "module",
        "",
        *[f"public import {m}" for m in decl.get("imports", [])],
        "",
        "@[expose] public section",
        "",
        f"namespace {decl['namespace']}",
        "open " + " ".join(["PTX PTX.Flow PTX.Proof", *decl.get("open", [])]),
        "",
        "noncomputable section",
        "",
    ]
    for inst in decl["instances"]:
        rdecl = json.loads((ROOT / inst["decl"]).read_text())
        run = next((r for r in rdecl["runs"] if r["name"] == inst["run"]), None)
        where = f"{inst['decl']}:{inst['run']}"
        if run is None:
            raise FamilyError(f"{where}: no such run")
        ops = [code[pc]["opcode"] for pc in range(run["start"], run["end"])]
        if ops != shape:
            raise FamilyError(f"{where}: shape {' '.join(ops)} is not the template's")
        keys = keys_of(code, ids, run, inst.get("prefix", ""))
        keys.update(inst.get("params", {}))
        lines += instance(body, keys, where).strip("\n").splitlines() + [""]
    lines += ["end", "", f"end {decl['namespace']}", ""]
    text = "\n".join(wrap_lines(lines))
    if text.count("\n") > 500:
        raise FamilyError(f"{decl['output']} would have more than 500 lines; split the instances")
    long = [x for x in text.splitlines() if len(x) > 100]
    if long:
        raise FamilyError(f"a line is longer than 100 columns: {long[0]}")
    return text
