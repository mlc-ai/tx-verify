# SPDX-License-Identifier: Apache-2.0
"""Value tables of site machines, generated from the PTX.

A site machine states the registers live at its sites with the values a table gives them. A
table that mirrors the code (each register's entry is the term the code computes from recorded
values, launch terms and loop state) closes the segments of `site_cases` by `rfl`. This
generator writes those entries for the registers a declared stretch of code assigns once.

It reads only the PTX (instruction order and register ids as `Tools/flow_gen.py` and
`Core/Source/Decode.lean` compute them) and a declaration (JSON):

    {"ptx": "Kernels/K/k.ptx", "namespace": "PTX.Kernels.K.Gen", "output": "Kernels/K/Gen.lean",
     "imports": ["Lemmas.Flow.Arith32"],
     "tables": [{"name": "upFirst", "params": "(lane tl u1 : BitVec 64)",
                 "start": 2796, "end": 2816,
                 "known": {"%r141": "lane", "%r6160": "tl", "%r1255": "u1"},
                 "before": {"%r9": "r9"}}]}

`before` gives the value before the stretch of a register a guarded instruction writes.

For each table it walks the instructions `start ≤ pc < end` in order (the stretch must be
straight-line: no branch), skips the event instructions, and for each local integer instruction
whose destination register is assigned once in the stretch writes the entry `(id, value)`. An
operand is a `known` register (its term: a recorded value, a launch term or a loop field, all as
`BitVec 64` bits; a known predicate register is a `Bool` term), a register assigned earlier in the
stretch (its term, inlined), or an immediate. The terms use the vocabulary of
`Lemmas/Flow/Arith32.lean` for 32-bit integer forms and of `Lemmas/Flow/Arith32Wide.lean` for the
wider and narrower ones (64-bit `add`, `mul.lo`, `shl`, `mov`; `mul.wide` by an immediate or a
register; `cvt` from 32 to 64 bits, from `s8` and from `u16`; `mul.hi.s32` by an immediate;
`div.u32`, `max.s32`, `or.b32`, `neg.s32`, shifts by a register; 16-bit literals and `xor` with 1);
a table that uses them imports that module. An entry's width is its instruction's (`.bits 64`,
`.bits 16`; `cvt.s32.s8` writes the vocabulary's `cvts8` value). A guarded instruction whose
destination is assigned once in the stretch writes `sel` of its guard term, the new value and the
register's value before the stretch, which must be declared. An operand of no kind, or an
instruction outside the vocabulary, stops the generator with the register or instruction it needs
declared. A table mirrors one path: an unguarded branch jumps, a guarded one goes the way the
declaration gives (`"branches": {"<pc>": true}` for taken), and an undeclared guarded branch, an
indexed branch, a loop or a path that leaves the stretch stops the generator.

    python Tools/machine_gen.py decl.json            # write the output
    python Tools/machine_gen.py decl.json --check    # fail if the output is stale
"""

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402
from lean_wrap import wrap_lines  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

CMP = {"eq": ".eq", "ne": ".ne", "lt": ".lt", "le": ".le", "gt": ".gt", "ge": ".ge"}
ITYPE = {"s32": ".s", "u32": ".u", "b32": ".b"}
WIDE = {"s64", "u64", "b64"}
SHORT = {"b16", "u16", "s16"}


class GenError(Exception):
    pass


def imm(text):
    return re.fullmatch(r"-?\d+", text) is not None


def lean_int(text):
    n = int(text)
    return f"({n})" if n < 0 else str(n)


class Stretch:
    """The entries of one table."""

    def __init__(self, code, ids, known, before=None):
        self.code, self.ids = code, ids
        self.bits = {}  # register -> BitVec 64 term
        self.preds = {}  # register -> Bool term
        self.before = dict(before or {})  # register -> its value before the stretch
        for r, term in known.items():
            (self.preds if r.startswith("%p") else self.bits)[r] = term

    def word(self, text):
        if imm(text):
            return f"(i32 {lean_int(text)})"
        if text in self.bits:
            return self.bits[text]
        raise GenError(f"operand {text} needs a declared term")

    def pred(self, text):
        if text in self.preds:
            return self.preds[text]
        raise GenError(f"predicate {text} needs a declared term")

    def binop(self, f, fi, a, b):
        if imm(b) and fi:
            return f"({fi} {self.word(a)} {lean_int(b)})"
        return f"({f} {self.word(a)} {self.word(b)})"

    def term(self, ins):
        """The bits or predicate the instruction computes, or `None` for no entry.

        Bits come with their width: `("bits", t)` is a 32-bit word, `("bits64", t)`,
        `("bits16", t)` the other widths, `("value", t, w)` a value term whose word for later
        operands is `w`."""
        op = ins["opcode"].split(".")
        o = ins["operands"]
        base = op[0]
        if base == "mov" and op[1] in ("u32", "b32", "s32"):
            return "bits", self.word(o[1])
        if base == "mov" and op[1] in WIDE and not imm(o[1]):
            return "bits64", self.word(o[1])
        if base == "mov" and op[1] in SHORT and imm(o[1]):
            return "bits16", f"(i16 {lean_int(o[1])})"
        if base == "add" and op[1] in ITYPE:
            return "bits", self.binop("add32", "addi", o[1], o[2])
        if base == "add" and op[1] in WIDE:
            return "bits64", self.binop("add64", "addi64", o[1], o[2])
        if base == "sub" and op[1] in ITYPE:
            return "bits", f"(sub32 {self.word(o[1])} {self.word(o[2])})"
        if base == "mul" and op[1:] == ["lo", "s32"]:
            return "bits", f"(mul32 {self.word(o[1])} {self.word(o[2])})"
        if base == "mul" and op[1] == "lo" and op[2] in WIDE and not imm(o[2]):
            return "bits64", f"(mul64 {self.word(o[1])} {self.word(o[2])})"
        if base == "mul" and op[1] == "wide" and op[2] in ("s32", "u32"):
            k = ITYPE[op[2]]
            if imm(o[2]):
                return "bits64", f"(mulWide {k} {self.word(o[1])} {lean_int(o[2])})"
            return "bits64", f"(mulWideR {k} {self.word(o[1])} {self.word(o[2])})"
        if base == "mul" and op[1:] == ["hi", "s32"] and imm(o[2]):
            return "bits", f"(mulhi {self.word(o[1])} {lean_int(o[2])})"
        if base == "mad" and op[1:] == ["lo", "s32"]:
            return "bits", f"(mad32 {self.word(o[1])} {self.word(o[2])} {self.word(o[3])})"
        if base == "min" and op[1] == "s32":
            return "bits", f"(min32 {self.word(o[1])} {self.word(o[2])})"
        if base == "max" and op[1] == "s32":
            return "bits", f"(max32 {self.word(o[1])} {self.word(o[2])})"
        if base == "neg" and op[1] == "s32":
            return "bits", f"(neg32 {self.word(o[1])})"
        if base == "div" and op[1] == "u32":
            return "bits", f"(divu {self.word(o[1])} {self.word(o[2])})"
        if base == "shr" and imm(o[2]) and op[1] in ITYPE:
            f = "shrs" if op[1] == "s32" else "shru"
            return "bits", f"({f} {self.word(o[1])} {lean_int(o[2])})"
        if base == "shr" and op[1] == "u32":
            return "bits", f"(shrur {self.word(o[1])} {self.word(o[2])})"
        if base == "shl" and op[1] == "b32" and imm(o[2]):
            return "bits", f"(shl {self.word(o[1])} {lean_int(o[2])})"
        if base == "shl" and op[1] == "b32":
            return "bits", f"(shlr {self.word(o[1])} {self.word(o[2])})"
        if base == "shl" and op[1] == "b64" and imm(o[2]):
            return "bits64", f"(shl64 {self.word(o[1])} {lean_int(o[2])})"
        if base == "and" and op[1] == "b32" and imm(o[2]):
            return "bits", f"(andi {self.word(o[1])} {lean_int(o[2])})"
        if base == "or" and op[1] == "b32":
            return "bits", f"(or32 {self.word(o[1])} {self.word(o[2])})"
        if base == "xor" and op[1] == "b32":
            return "bits", f"(xor32 {self.word(o[1])} {self.word(o[2])})"
        if base == "xor" and op[1] in SHORT and o[2] == "1":
            return "bits16", f"(xor16 {self.word(o[1])})"
        if base == "not" and op[1] == "b32":
            return "bits", f"(not32 {self.word(o[1])})"
        if base == "popc" and op[1] == "b32":
            return "bits", f"(popc {self.word(o[1])})"
        if base == "cvt" and op[1:] == ["s64", "s32"]:
            return "bits64", f"(sext {self.word(o[1])})"
        if base == "cvt" and op[1:] == ["u64", "u32"]:
            return "bits64", f"(zext {self.word(o[1])})"
        if base == "cvt" and op[1:] == ["u32", "u16"]:
            return "bits", f"(zext16 {self.word(o[1])})"
        if base == "cvt" and op[1:] == ["s32", "s8"]:
            x = self.word(o[1])
            return "value", f"(cvts8 {x})", f"(cvts8w {x})"
        if base == "selp" and op[1] == "b32":
            return "bits", f"(sel {self.pred(o[3])} {self.word(o[1])} {self.word(o[2])})"
        if base == "setp" and op[1] in CMP and op[2] in ITYPE:
            c, k = CMP[op[1]], ITYPE[op[2]]
            if imm(o[2]):
                return "pred", f"(scmpi {c} {k} {self.word(o[1])} {lean_int(o[2])})"
            return "pred", f"(scmp {c} {k} {self.word(o[1])} {self.word(o[2])})"
        if base == "and" and op[1] == "pred":
            return "pred", f"({self.pred(o[1])} && {self.pred(o[2])})"
        if base == "not" and op[1] == "pred":
            return "pred", f"(!{self.pred(o[1])})"
        raise GenError(f"pc {ins['pc']}: no term for {ins['opcode']}")

    def guarded(self, ins, reg, t):
        """The term of a guarded instruction: its value where the guard holds, else the
        register's value before the stretch (declared)."""
        if reg not in self.before:
            raise GenError(
                f"pc {ins['pc']}: guarded {reg} needs its value before the stretch declared"
            )
        g = self.pred(ins["guard"]["register"])
        if ins["guard"]["negated"]:
            g = f"(!{g})"
        return f"(sel {g} {t} {self.before[reg]})"

    def path(self, start, end, branches):
        """The instructions of the stretch along one path: an unguarded branch jumps, a guarded
        one goes the declared way (`branches`: pc → taken), and the path ends at `end`."""
        out, seen, pc = [], set(), start
        while pc != end:
            if not start <= pc < end:
                raise GenError(f"pc {pc}: the path leaves the stretch")
            if pc in seen:
                raise GenError(f"pc {pc}: the path loops")
            seen.add(pc)
            ins = self.code[pc]
            if ins["table"] is not None:
                raise GenError(f"pc {pc}: an indexed branch has no table form")
            if ins["target"] is not None:
                if ins["guard"] is None:
                    pc = ins["target"]
                elif str(pc) in branches:
                    pc = ins["target"] if branches[str(pc)] else pc + 1
                else:
                    raise GenError(f"pc {pc}: the branch needs a declared direction")
                continue
            out.append(ins)
            pc += 1
        return out

    def entries(self, start, end, branches=None):
        stretch = self.path(start, end, branches or {})
        writes = {}
        for ins in stretch:
            for w in ins["writes"]:
                writes[w] = writes.get(w, 0) + 1
        out = []
        for ins in stretch:
            if ins["event"] or len(ins["writes"]) != 1:
                continue
            reg = ins["writes"][0]
            if writes[reg] != 1 or reg in self.bits or reg in self.preds:
                continue
            res = self.term(ins)
            kind, t = res[0], res[1]
            if ins["guard"] is not None:
                if kind not in ("bits", "bits64", "bits16"):
                    raise GenError(f"pc {ins['pc']}: guarded {ins['opcode']} has no table form")
                t = self.guarded(ins, reg, t)
            width = {"bits": 32, "bits64": 64, "bits16": 16}
            if kind in width:
                self.bits[reg] = t
                out.append((self.ids[reg], f".bits {width[kind]} {t}", reg))
            elif kind == "value":
                self.bits[reg] = res[2]
                out.append((self.ids[reg], t, reg))
            else:
                self.preds[reg] = t
                out.append((self.ids[reg], f".pred {t}", reg))
        return out


def render(decl):
    ptx = ROOT / decl["ptx"]
    program = parse_ptx.parse(ptx.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        f"-- Generated by Tools/machine_gen.py from {decl['ptx']}; do not edit.",
        "module",
        "",
        *[f"public import {m}" for m in decl.get("imports", ["Lemmas.Flow.Arith32"])],
        "",
        "@[expose] public section",
        "",
        f"namespace {decl['namespace']}",
        "open PTX PTX.Flow.Arith32",
        "",
        "noncomputable section",
        "",
    ]
    for t in decl["tables"]:
        st = Stretch(code, ids, t.get("known", {}), t.get("before", {}))
        rows = st.entries(t["start"], t["end"], t.get("branches", {}))
        lines.append(f"/-- The registers pcs {t['start']}–{t['end'] - 1} assign once. -/")
        lines.append(f"def {t['name']} {t.get('params', '')} : List (Nat × Value) := [".rstrip())
        for i, (rid, val, reg) in enumerate(rows):
            sep = "," if i + 1 < len(rows) else ""
            lines.append(f"  ({rid}, {val}){sep}  -- {reg}")
        lines.append("]")
        lines.append("")
    lines += ["end", "", f"end {decl['namespace']}", ""]
    return "\n".join(wrap_lines(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("decl", type=Path)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    decl = json.loads(args.decl.read_text())
    try:
        text = render(decl)
    except GenError as e:
        sys.exit(f"machine_gen: {e}")
    out = ROOT / decl["output"]
    if args.check:
        if not out.exists() or out.read_text() != text:
            sys.exit(f"machine_gen: {decl['output']} is stale; rerun Tools/machine_gen.py")
        return
    out.write_text(text)


if __name__ == "__main__":
    main()
