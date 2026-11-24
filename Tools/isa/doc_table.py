# SPDX-License-Identifier: Apache-2.0
"""The per-instruction tables of docs/core: coverage of the instruction entries and the tables.

    python3 Tools/isa/doc_table.py --write    # run the coverage and write isa-coverage.json
    python3 Tools/isa/doc_table.py --check    # run the coverage and compare with the JSON

Coverage. For every instruction entry of the vendored table and every legal modifier combination
(`variants`), `samples` writes one instruction with sample operands (registers named after the
type of the operand, so that the decoder's environment can declare them at the right widths).
`Tests/Source/IsaCoverage.lean` decodes each line with `Decode.op` and prints its status: `core <ID>`
when `Op.rule` names a contract entry, `decode-only`, or `rejected <reason>`.
`coverage` compresses the statuses of one entry into disjoint cubes of equal status and
`docs/core/isa-coverage.json` records them. It also records the status of every special register
(the input line `sregs`): whether the decoder accepts a `mov` from it and, if so, the rule
`SReg.rule` names and the kind of value `SReg.kind` gives.

Tables. `render_tables` reads that JSON and the entry data and writes, for each instruction
family, one table with a row per entry (see `Tools/coredoc.py`, which places the tables in the
chapters).
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import itertools
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import constraints  # noqa: E402

COVERAGE = ROOT / "docs" / "core" / "isa-coverage.json"
DRIVER = ROOT / "Tests" / "Source" / "IsaCoverage.lean"

# ----------------------------------------------------------------------------- samples


def operand_groups(entry):
    """The operands of an entry as groups: ("single", [op]), ("pipe", [ops]), ("bracket", [ops])."""
    ops = entry["operands"]
    groups = []
    i = 0
    while i < len(ops):
        for kind in ("pipe", "bracket"):
            if ops[i][kind] is not None:
                j = i
                while j < len(ops) and ops[j][kind] == ops[i][kind]:
                    j += 1
                groups.append((kind, ops[i:j]))
                i = j
                break
        else:
            groups.append(("single", [ops[i]]))
            i += 1
    return groups


def type_width(token):
    """The width in bits of the type of a `.size` or `.type` token (`u32`, `b64`, ...)."""
    m = re.fullmatch(r"[busf](\d+)", token or "")
    return int(m.group(1)) if m else {"bf16": 16}.get(token or "")


def address_width(entry, op, combo):
    """The width of the register of an address or pointer operand: the operand's state space, or
    the state space or the size written in the modifiers."""
    space = op["space"]
    if space == "global":
        return 64
    if space and space.startswith("shared"):
        return 32
    slots = [s[0] for s in entry["slots"]]
    if entry["family"] == "tc":
        return 32
    if op["kind"] in ("ptr", "var") and "type" in slots:
        w = type_width(combo[slots.index("type")])
        if w in (32, 64):
            return w
    return 32 if any(t.startswith("shared") for t in combo) else 64


def sample_operands(entry, vi):
    """The written operands (as the line encoding of `Tests/Source/IsaCoverage.lean`) of the variant
    `vi` of an entry: distinct registers named `%<type>_<n>`, `[r]` addresses, the first allowed
    immediate, the label `L`, the table `T`."""
    combo = entry["variants"][vi]
    slots = [s[0] for s in entry["slots"]]
    count = itertools.count()
    is_param = entry["name"].startswith("ld_param")
    vec = any(t in ("v2", "v4", "v8") for t in combo)

    def register(op):
        d = constraints.normal_dtype(op["dtype"][vi]) if op["dtype"][vi] is not None else None
        if d is not None:
            return f"r%{d}_{next(count)}"
        return f"r%A{address_width(entry, op, combo)}_{next(count)}"

    def one(op, inner):
        k = op["kind"]
        lanes = op["lanes"][vi]
        if k in ("reg", "regvar"):
            r = register(op)
            if op["group"]:
                return "v(" + ",".join(register(op) for _ in range(lanes)) + ")"
            return r
        if k == "addr":
            if is_param:
                t = combo[slots.index("type")]
                w = type_width(t) or 32
                r = f"s{'O' if vec else 'P'}{w}"
            else:
                r = register(op)
            return r if inner else "a(" + r + ")"
        if k in ("ptr", "var"):
            return register(op)
        if k == "imm":
            if op["literal"] == "_":
                return "_"
            first = (op["choices"] or [op["literal"] or "0"])[0]
            return "l" + str(first)
        return "sT" if op["name"] == "tlist" else "sL"

    out = []
    for kind, members in operand_groups(entry):
        if kind == "single":
            if members[0]["lanes"][vi] == 0:
                continue
            out.append(one(members[0], False))
        else:
            inner = ",".join(one(op, True) for op in members)
            out.append(("p(" if kind == "pipe" else "a(") + inner + ")")
    return out


def sample_line(entry, vi, entry_id):
    """One line of the input of `Tests/Source/IsaCoverage.lean`: the expected entry, the opcode and the
    operands, separated by tabs."""
    combo = entry["variants"][vi]
    opcode = ".".join([entry["mnemonic"], *[t for t in combo if t]])
    return "\t".join([entry_id, opcode, *sample_operands(entry, vi)])


def run_lean(lines, root=ROOT, jobs=16):
    """The statuses `Tests/Source/IsaCoverage.lean` prints for the input lines, computed by `jobs`
    processes on consecutive chunks."""
    size = max(1, -(-len(lines) // jobs))
    chunks = [lines[i : i + size] for i in range(0, len(lines), size)]
    with ThreadPoolExecutor(len(chunks) or 1) as pool:
        parts = list(pool.map(lambda c: run_lean_chunk(c, root), chunks))
    return [s for part in parts for s in part]


def run_lean_chunk(lines, root):
    """The statuses of one chunk, from one `lean --run` process."""
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env.get("PATH", "")
    if "ISA_LEAN_PATH" in env:
        env["LEAN_PATH"] = env["ISA_LEAN_PATH"]
    else:
        lp = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=root,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        env["LEAN_PATH"] = lp.stdout.strip()
    res = subprocess.run(
        ["lean", "-s512000", "--run", str(root / "Tests" / "Source" / "IsaCoverage.lean")],
        cwd=root,
        env=env,
        input="".join(line + "\n" for line in lines),
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        raise SystemExit("lean failed:\n" + res.stdout[-3000:] + res.stderr[-3000:])
    out = res.stdout.splitlines()
    if len(out) != len(lines):
        raise SystemExit(f"lean printed {len(out)} statuses for {len(lines)} instructions")
    return out


# ----------------------------------------------------------------------------- compression


def cubes_of(points, n):
    """Disjoint cubes (tuples of sorted value lists) whose union is exactly `points`."""
    raw = constraints._decompose(set(points), list(range(n)))
    cs = sorted((tuple(c[k] for k in range(n)) for c in raw), key=constraints._order)
    return [tuple(sorted(s) for s in c) for c in constraints._merge(cs, n)]


def operand_text(entry):
    """The operands of an entry in syntax order: `[a]` an address, `{d0, ...}` a register group,
    `d|p` a pipe pair, `{x}` an operand some combinations omit."""
    out = []
    for kind, members in operand_groups(entry):

        def one(op, inner=False):
            n = op["name"]
            if op["kind"] == "imm" and op["literal"] is not None:
                n = op["literal"]
            if op["group"]:
                n = "{" + n + "...}"
            if op["kind"] == "addr" and not inner:
                n = f"[{n}]"
            if 0 in op["lanes"] and any(op["lanes"]):
                n = "{" + n + "}"
            return n

        if kind == "single":
            if any(members[0]["lanes"]):
                out.append(one(members[0]))
        elif kind == "pipe":
            out.append("|".join(one(op, True) for op in members))
        else:
            out.append("[" + ", ".join(one(op, True) for op in members) + "]")
    return ", ".join(out)


def normal_status(status):
    """A status without the register names of its reason."""
    return re.sub(r"%\w+_\d+", "%reg", status)


def sreg_statuses(text):
    """The special register records of the `sregs` line that `Tests/Source/IsaCoverage.lean` prints."""
    out = []
    for item in text.split(";"):
        name, _, status = item.partition("=")
        out.append({"name": name, "status": status})
    return out


def coverage(final=None, statuses=None, sregs=None):
    """The coverage record of the decoded entries, the excluded ones and the special registers.
    `statuses` is the list of statuses, one per variant of every entry in order, and `sregs` the
    `sregs` line (default: run the Lean test)."""
    import gen_lean

    m = gen_lean.build_model(final)
    lines, index = [], []
    for e in m.entries:
        for vi in range(len(e["variants"])):
            lines.append(sample_line(e, vi, m.entry_id[e["name"]]))
            index.append(e["name"])
    if statuses is None:
        *result, sregs = run_lean([*lines, "sregs"])
    else:
        result = statuses
    by_entry = {}
    for name, st in zip(index, result, strict=True):
        by_entry.setdefault(name, []).append(normal_status(st))
    entries = {}
    for e in m.entries:
        sts = by_entry[e["name"]]
        n = len(e["slots"])
        groups = {}
        for combo, st in zip(e["variants"], sts, strict=True):
            groups.setdefault(st, []).append(combo)
        entries[e["name"]] = {
            "head": {
                "family": e["family"],
                "mnemonic": e["mnemonic"],
                "effect": e["effect"],
                "section": e["section"],
                "slots": [[s[0], bool(s[2])] for s in e["slots"]],
                "operands": operand_text(e),
                "combinations": len(sts),
            },
            "statuses": [
                {"status": st, "count": len(pts), "cubes": cubes_of(pts, n)}
                for st, pts in sorted(groups.items(), key=lambda kv: (-len(kv[1]), kv[0]))
            ],
        }
    excluded = {}
    for e in m.excluded:
        key = (e["mnemonic"].split(".")[0], e["reason"])
        excluded.setdefault(key, set()).add(e["section"])
    return {
        "entries": entries,
        "excluded": [
            {"mnemonic": a, "reason": b, "sections": sorted(secs)}
            for (a, b), secs in sorted(excluded.items())
        ],
        "sregs": sreg_statuses(sregs) if sregs is not None else [],
    }


def dump(cov):
    """The text of isa-coverage.json: one line per entry head and per status."""
    sep = (",", ":")
    out = ['{"entries": {']
    names = list(cov["entries"])
    for i, name in enumerate(names):
        r = cov["entries"][name]
        out.append(f"{json.dumps(name)}: {{")
        out.append('"head": ' + json.dumps(r["head"], separators=sep) + ",")
        out.append('"statuses": [')
        out.append(",\n".join(json.dumps(s, separators=sep) for s in r["statuses"]))
        out.append("]")
        out.append("}" + ("," if i + 1 < len(names) else ""))
    out.append('}, "excluded": [')
    out.append(",\n".join(json.dumps(x, separators=sep) for x in cov["excluded"]))
    out.append('], "sregs": [')
    out.append(",\n".join(json.dumps(x, separators=sep) for x in cov.get("sregs", [])))
    out.append("]}")
    return "\n".join(out) + "\n"


def load(path=COVERAGE):
    return json.loads(Path(path).read_text())


# ----------------------------------------------------------------------------- tables

# The order of the rows of a table: families in this order, entries by mnemonic then name.
MARK = {"core": "Core semantics", "decode-only": "Decode only"}


def kind_of(status):
    return status.split(" ")[0]


def slot_values(record, kinds):
    """The values of every slot in the combinations whose status kind is in `kinds`."""
    n = len(record["head"]["slots"])
    vals = [set() for _ in range(n)]
    for st in record["statuses"]:
        if kind_of(st["status"]) in kinds:
            for cube in st["cubes"]:
                for k in range(n):
                    vals[k].update(cube[k])
    return vals


def shown(v):
    return f"`{v}`" if v else "(omitted)"


def modifier_cell(record):
    """The modifier values with semantics and those that decode only, per slot."""
    names = [s[0] for s in record["head"]["slots"]]
    core = slot_values(record, ("core",))
    dec = slot_values(record, ("decode-only",))
    parts = []
    for title, sets in (
        ("With semantics", core),
        ("Decode only", [d - c for d, c in zip(dec, core, strict=True)]),
    ):
        lines = []
        for name, vals in zip(names, sets, strict=True):
            if vals:
                lines.append(f"{name}: " + ", ".join(shown(v) for v in sorted(vals)))
        if lines:
            parts.append(f"**{title}:** " + "; ".join(lines))
    return "<br>".join(parts) if parts else "none"


def syntax(record):
    h = record["head"]
    return h["mnemonic"] + "".join(("{." + n + "}") if opt else ("." + n) for n, opt in h["slots"])


def status_cell(record):
    h = record["head"]
    count = {"core": 0, "decode-only": 0, "rejected": 0}
    for st in record["statuses"]:
        count[kind_of(st["status"])] += st["count"]
    total = h["combinations"]
    ruled = count["core"]
    text = []
    if ruled:
        text.append("Core semantics" + ("" if ruled == total else f" ({ruled} of {total})"))
    if count["decode-only"]:
        why = (
            "an `Assumption.localRule` may give it a meaning"
            if h["effect"] == "local"
            else "execution is rejected"
        )
        label = "Decode only" if not ruled else f"Decode only ({count['decode-only']} of {total})"
        text.append(f"{label}: {why}")
    if count["rejected"]:
        reasons = sorted(
            {st["status"].removeprefix("rejected ") for st in record["statuses"]}
            - {s for s in MARK}
        )
        reasons = [r for r in reasons if not r.startswith(("core", "decode-only"))]
        text.append(f"Rejected at decoding ({count['rejected']} of {total}): " + "; ".join(reasons))
    return "<br>".join(text)


def rule_cell(record, link):
    ids = []
    for st in record["statuses"]:
        k, _, rest = st["status"].partition(" ")
        if k == "core" and rest not in ids:
            ids.append(rest)
    out = []
    for i in ids:
        target = link(i)
        out.append(f"[{i}]({target})" if target else i)
    return ", ".join(out) if out else "none"


def esc(text):
    return text.replace("|", "\\|")


def render_family_table(cov, families, link):
    """The lines of the table of the entries of `families`."""
    rows = [
        (name, rec) for name, rec in cov["entries"].items() if rec["head"]["family"] in families
    ]
    rows.sort(
        key=lambda r: (families.index(r[1]["head"]["family"]), r[1]["head"]["mnemonic"], r[0])
    )
    out = [
        "| Instruction | Modifiers | Operands | Kind | Status | Rule | Manual |",
        "|---|---|---|---|---|---|---|",
    ]
    for name, rec in rows:
        h = rec["head"]
        kind = {"local": "local", "event": "event", "ctl": "control"}[h["effect"]]
        cells = [
            f"`{syntax(rec)}`",
            modifier_cell(rec),
            f"`{h['operands']}`" if h["operands"] else "none",
            kind,
            status_cell(rec),
            rule_cell(rec, link),
            f"§{h['section']}",
        ]
        out.append("| " + " | ".join(esc(c) for c in cells) + " |")
    return out


def render_excluded(cov):
    out = ["| Instruction | Reason | Manual |", "|---|---|---|"]
    for x in cov["excluded"]:
        sections = ", ".join(f"§{sec}" for sec in x["sections"])
        out.append(f"| `{x['mnemonic']}` | {x['reason']} | {sections} |")
    return out


SREG_VALUE = {
    "launch": "the thread's position in the launch",
    "lane": "the thread's lane in its warp",
    "initial": "fixed before launch, unconstrained (`Launch.sregInit`)",
    "varying": "changes while the thread runs; each read is an event with an open value",
}

# Registers numbered within one row: `%pm0`...`%pm7`, `%pm0_64`...`%pm7_64`, `%envreg<32>`,
# `%reserved_smem_offset_<2>`.
NUMBERED = re.compile(r"(%pm|%envreg|%reserved_smem_offset_)(\d+)(_64)?")


def sreg_rows(cov):
    """The special registers as rows (name, status), with the numbered registers of one prefix
    and status merged into a range."""
    rows = []
    for r in cov.get("sregs", []):
        m = NUMBERED.fullmatch(r["name"])
        if m and rows and rows[-1][2] == (m.group(1), m.group(3)) and rows[-1][1] == r["status"]:
            first = rows[-1][0].split("–")[0]
            rows[-1] = (f"{first}–{r['name']}", r["status"], rows[-1][2])
        else:
            rows.append((r["name"], r["status"], (m.group(1), m.group(3)) if m else None))
    return [(name, status) for name, status, _ in rows]


def render_sreg_table(cov, link):
    """The lines of the table of the special registers."""
    out = ["| Register | Status | Value | Rule |", "|---|---|---|---|"]
    for name, status in sreg_rows(cov):
        kind, _, rest = status.partition(" ")
        if kind == "core":
            ident, _, value = rest.partition(" ")
            target = link(ident)
            cells = [
                "Core semantics",
                SREG_VALUE[value],
                f"[{ident}]({target})" if target else ident,
            ]
        elif kind == "decode-only":
            cells = ["Decode only: an `Assumption.localRule` may give it a meaning", "none", "none"]
        else:
            cells = [f"Rejected at decoding: {rest}", "none", "none"]
        out.append("| " + " | ".join(esc(c) for c in [f"`{name}`", *cells]) + " |")
    return out


def sreg_counts(cov):
    """(registers with Core semantics, registers that decode only, registers rejected)."""
    kinds = [kind_of(r["status"]) for r in cov.get("sregs", [])]
    return kinds.count("core"), kinds.count("decode-only"), kinds.count("rejected")


def counts(cov, families):
    """(entries with Core semantics, entries that decode only, entries rejected) of `families`."""
    core = dec = rej = 0
    for rec in cov["entries"].values():
        if rec["head"]["family"] not in families:
            continue
        kinds = {kind_of(s["status"]) for s in rec["statuses"]}
        if "core" in kinds:
            core += 1
        elif "decode-only" in kinds:
            dec += 1
        else:
            rej += 1
    return core, dec, rej


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--write", action="store_true")
    cli.add_argument("--check", action="store_true")
    args = cli.parse_args()
    text = dump(coverage())
    if args.write:
        COVERAGE.write_text(text)
    elif args.check and COVERAGE.read_text() != text:
        raise SystemExit("docs/core/isa-coverage.json is stale: run Tools/isa/doc_table.py --write")


if __name__ == "__main__":
    main()
