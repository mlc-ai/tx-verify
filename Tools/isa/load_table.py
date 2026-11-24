# SPDX-License-Identifier: Apache-2.0
"""Vendor the TIRx PTX instruction table as data, and load the vendored data.

`python3 Tools/isa/load_table.py --vendor <path>/table.py` loads the table module by path with
`importlib` (the module imports nothing from tvm) and writes `Tools/isa/data/table.json`. Every
part of the table that is a Python function is evaluated here, once:

* `variants()` (the slot product filtered by the entry's `check`) becomes the list of legal
  modifier combinations of the entry;
* for every operand and every legal combination, the resolved PTX type token (`operand_type`,
  only for register operands), the number of registers (`lanes`) and whether a lane may be the
  sink `_` (`sinkable`) become per-combination facts.

The JSON records the table's path, git commit and sha256. Nothing in the build imports tvm or
table.py; the other tools read the JSON through `load()`.

Encoding. A combination is a string with one character per slot: `0` when the slot is omitted
and otherwise the base-62 digit of `1 + index` of the chosen token in the slot's choices. A
per-combination fact is either one constant value or a pair `[values, codes]` where `codes` has
one base-62 digit per combination, indexing `values`.
"""

import argparse
import hashlib
import importlib.util
import inspect
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE / "data" / "table.json"
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"


def encode_combo(slots, combo):
    """`combo` is a tuple of tokens (`""` = omitted) aligned with `slots` ([name, choices, opt])."""
    out = []
    for (_, choices, _), tok in zip(slots, combo, strict=True):
        out.append(DIGITS[0] if tok == "" else DIGITS[1 + choices.index(tok)])
    return "".join(out)


def decode_combo(slots, code):
    return tuple(
        "" if c == "0" else choices[DIGITS.index(c) - 1]
        for (_, choices, _), c in zip(slots, code, strict=True)
    )


def encode_column(values):
    """A per-combination fact column: a constant, or `[distinct values, codes]`."""
    distinct = []
    for v in values:
        if v not in distinct:
            distinct.append(v)
    if len(distinct) == 1:
        return distinct[0]
    if len(distinct) > len(DIGITS):
        raise ValueError("too many distinct fact values")
    return [distinct, "".join(DIGITS[distinct.index(v)] for v in values)]


def decode_column(column, n):
    if isinstance(column, list) and len(column) == 2 and isinstance(column[1], str):
        values, codes = column
        if len(codes) != n:
            raise ValueError("fact column length")
        return [values[DIGITS.index(c)] for c in codes]
    return [column] * n


def _load_module(path: Path):
    spec = importlib.util.spec_from_file_location("ptx_table_vendored", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["ptx_table_vendored"] = module
    spec.loader.exec_module(module)
    return module


def _git_commit(path: Path) -> str:
    out = subprocess.run(
        ["git", "-C", str(path.parent), "log", "-1", "--format=%H", "--", path.name],
        capture_output=True,
        text=True,
        check=True,
    )
    dirty = subprocess.run(
        ["git", "-C", str(path.parent), "status", "--porcelain", "--", path.name],
        capture_output=True,
        text=True,
        check=True,
    )
    commit = out.stdout.strip()
    if dirty.stdout.strip():
        raise SystemExit(f"{path} has uncommitted changes; vendor a committed table")
    return commit


def _operand(m, op, combos, entry):
    """Static description of one operand plus its per-combination facts."""
    group = op.vector if op.vector is not None else (callable(op.lanes) or op.lanes > 1)
    d = {
        "name": op.name,
        "kind": op.kind,
        "rw": op.rw,
        "space": op.space,
        "literal": op.literal,
        "choices": list(op.choices) if op.choices is not None else None,
        "bracket": op.bracket,
        "pipe": op.pipe,
        "group": bool(group),
        "imm_offset": op.allow_imm_offset,
    }
    lanes, dtypes, sinks = [], [], []
    for combo in combos:
        mm = m.mods(entry, combo)
        lanes.append(m.lanes_of(op, mm))
        if op.kind == "reg":
            dtypes.append(m.operand_type(op, mm))
        else:
            dtypes.append(op.dtype if isinstance(op.dtype, str) else None)
        s = op.sinkable(mm) if callable(op.sinkable) else op.sinkable
        sinks.append(bool(s))
    d["lanes"] = encode_column(lanes)
    d["dtype"] = encode_column(dtypes)
    d["sink"] = encode_column(sinks)
    return d


def vendor(path: Path, out: Path = DATA):
    path = path.resolve()
    m = _load_module(path)
    entries = []
    for name, e in m.TABLE.items():
        slots = [[s.name, list(s.choices), bool(s.optional)] for s in e.slots]
        combos = list(m.variants(e))
        if not combos:
            raise SystemExit(f"{name}: no legal modifier combination")
        doc = inspect.cleandoc(e.check.__doc__) if e.check is not None and e.check.__doc__ else ""
        entries.append(
            {
                "name": name,
                "mnemonic": e.ptx_name,
                "cert_arch": e.cert_arch,
                "orders_memory": bool(e.orders_memory),
                "check": doc,
                "slots": slots,
                "operands": [_operand(m, op, combos, e) for op in e.operands],
                "variants": [encode_combo(slots, c) for c in combos],
            }
        )
    source = {
        "path": "tvm/python/tvm_tirx/backend/cuda/ptx/table.py",
        "commit": _git_commit(path),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }
    write(out, source, entries)
    return source, len(entries)


def write(out: Path, source, entries):
    """One entry per line, so that a table revision gives a readable diff."""
    lines = ['{"source": ' + json.dumps(source, sort_keys=True) + ',\n "entries": [']
    body = [json.dumps(e, separators=(",", ":")) for e in entries]
    lines.append(",\n".join(body))
    lines.append("]}\n")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(lines))


def load(path: Path = DATA):
    """The vendored table: `{"source": ..., "entries": [...]}` with every entry's variants
    decoded to token tuples and every operand fact decoded to one value per variant."""
    raw = json.loads(path.read_text())
    for e in raw["entries"]:
        e["variants"] = [decode_combo(e["slots"], c) for c in e["variants"]]
        n = len(e["variants"])
        for op in e["operands"]:
            for key in ("lanes", "dtype", "sink"):
                op[key] = decode_column(op[key], n)
    return raw


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--vendor", type=Path, required=True, help="path of table.py")
    args = cli.parse_args()
    source, n = vendor(args.vendor)
    print(f"vendored {n} entries from {source['path']} at {source['commit']}")


if __name__ == "__main__":
    main()
