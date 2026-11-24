# SPDX-License-Identifier: Apache-2.0
"""Value-table entries for the floating registers a local segment writes.

A site machine states the registers live at a program counter with the values a table gives
them. Along a local segment whose instructions compute with floats, `seg_fp` evaluates the
code and leaves, for every written register that is live at the end, an equation between the
computed value and the table's. When the table writes the computed term itself (the same
operations on the same operands, in code order), the equation closes by `rfl`; no
normalization of real terms (`ring_nf`) is needed. This generator writes those terms.

It reads only the PTX file (instruction order, register ids and liveness as
`Tools/flow_gen.py` computes them) and a JSON file giving the start values of the registers
the segment reads:

    {"%r944": {"real": "d.s 2"},                       // .float .f32 (d.s 2)
     "%r12":  {"real": "x", "fmt": "f16"},            // .float .f16 x
     "%rd169": {"pair": [{"real": "c"}, {"real": "c"}]},
     "%r5":   {"value": "b32 7"}}                       // any other value, copied only

and walks the instructions from `--start` up to (not including) `--end`, following
unconditional branches and the conditional branches and guards whose predicate `--pred`
gives. It prints one entry `(id, term),  -- name` for each register written along the way and
live at the end.

The terms are those of the core's data movement (`mov`, `pack`, `unpack`) and of the
ideal-real rules (ASM-IDEAL: `add`, `sub`, `mul`, `fma` of `.f32` and `.f32x2`, `min`/`max`
of two or three sources, `cvt.f32.f16`, `cvt.rn.f16x2.f32`, float `setp`), written in their
reduced form (`.pair` for a pack of floats, `max (max x y) z`): the computed value is the
same term up to reduction, so the equation closes by `rfl`. Forms without such a rule (an
integer instruction, `ex2.approx`, a directed rounding of `.f32x2`) stop the generator unless
`--templates` names their result:

    {"ex2.approx.ftz.f32": {"fmt": "f32", "real": "2 ^ {0}"}}

(`{i}` is the real number of source operand `i`). Integer values are not generated: a table
states them as numbers (`b32 n`), closed by `norm_bits`.

    python Tools/value_table.py k.ptx --start tmemLoad_3 --end barArrive_0 --inputs in.json
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402


class TableError(Exception):
    pass


@dataclass(frozen=True)
class Float:
    fmt: str
    real: str

    def lean(self) -> str:
        return f".float .{self.fmt} ({self.real})"


@dataclass(frozen=True)
class Pair:
    lo: object
    hi: object

    def lean(self) -> str:
        return f".pair ({self.lo.lean()}) ({self.hi.lean()})"


@dataclass(frozen=True)
class Opaque:
    term: str

    def lean(self) -> str:
        return self.term


@dataclass(frozen=True)
class Pred:
    term: str

    def lean(self) -> str:
        return f".pred ({self.term})"


def parse_value(spec, where: str):
    if not isinstance(spec, dict):
        raise TableError(f"{where}: expected an object, got {spec!r}")
    if "real" in spec:
        return Float(spec.get("fmt", "f32"), spec["real"])
    if "pair" in spec:
        lo, hi = spec["pair"]
        return Pair(parse_value(lo, where), parse_value(hi, where))
    if "value" in spec:
        return Opaque(spec["value"])
    raise TableError(f"{where}: expected `real`, `pair` or `value`")


CMP = {
    "eq": "eq",
    "ne": "ne",
    "lt": "lt",
    "le": "le",
    "gt": "gt",
    "ge": "ge",
    "equ": "eq",
    "neu": "ne",
    "ltu": "lt",
    "leu": "le",
    "gtu": "gt",
    "geu": "ge",
}

ROUNDINGS = {"rn", "rz", "rm", "rp"}


LITERAL = re.compile(r"^-?(0[fFdDxX][0-9a-fA-F]+|\d+(\.\d*)?)$")


def operand_regs(ins):
    """Source operands, each as its text and its resolved register names (a vector gives
    several; `None` for an immediate or a special register), in the order `flow_gen` lists the
    instruction's reads."""
    reads = list(ins["reads"])
    out = []
    for text in ins["operands"][1:]:
        regs = []
        for n in (t for t in re.split(r"[{},]", text) if t):
            if LITERAL.match(n) or flow_gen.SPECIAL.match(n):
                regs.append(None)
                continue
            if not reads:
                raise TableError(f"pc {ins['pc']}: operand {text} not resolved")
            regs.append(reads.pop(0))
        out.append((text, regs))
    return out


def dest_regs(ins):
    return list(ins["writes"])


class Walker:
    def __init__(self, ptx: Path, templates: dict):
        program = parse_ptx.parse(ptx.read_text())
        function = next(f for f in program.functions if not f.declaration)
        self.code = flow_gen.flatten(function)
        self.ids = flow_gen.register_ids(function)
        self.sites = {s["name"]: s["pc"] for s in flow_gen.sites(self.code)}
        self.templates = templates
        self._live = None

    def live(self, pc: int):
        if self._live is None:
            self._live = flow_gen.liveness(self.code)
        return self._live[pc]

    def pc_of(self, spec: str, after_site: bool) -> int:
        if spec.startswith("pc:"):
            return int(spec[3:])
        if spec not in self.sites:
            raise TableError(f"unknown site {spec}")
        return self.sites[spec] + (1 if after_site else 0)

    def value(self, env, reg, pc):
        if reg not in env:
            raise TableError(f"pc {pc}: no start value for {reg}")
        return env[reg]

    def real(self, v, fmt, pc, what):
        if not isinstance(v, Float) or v.fmt != fmt:
            raise TableError(f"pc {pc}: {what} is not a .{fmt} float ({v})")
        return v.real

    def step(self, ins, env, preds):
        pc = ins["pc"]
        opcode = ins["opcode"]
        parts = opcode.split(".")
        head = parts[0]
        dests = dest_regs(ins)
        srcs = operand_regs(ins)

        def src(i):
            text, regs = srcs[i]
            if len(regs) != 1 or regs[0] is None:
                raise TableError(f"pc {pc}: operand {text} of {opcode} is not one register")
            return self.value(env, regs[0], pc)

        def reals(fmt, n):
            return [self.real(src(i), fmt, pc, f"operand {i} of {opcode}") for i in range(n)]

        def pairs(n):
            out = []
            for i in range(n):
                v = src(i)
                if not isinstance(v, Pair):
                    raise TableError(f"pc {pc}: operand {i} of {opcode} is not a pair ({v})")
                out.append(
                    (
                        self.real(v.lo, "f32", pc, f"low half of operand {i}"),
                        self.real(v.hi, "f32", pc, f"high half of operand {i}"),
                    )
                )
            return out

        mods = parts[1:]
        last = mods[-1] if mods else ""
        rounding = next((m for m in mods if m in ROUNDINGS), None)
        if opcode in self.templates:
            t = self.templates[opcode]
            args = [src(i) for i in range(len(srcs))]
            rs = [a.real if isinstance(a, Float) else a.lean() for a in args]
            return {dests[0]: Float(t.get("fmt", "f32"), t["real"].format(*rs))}
        if head == "mov" and len(dests) == 2:
            v = src(0)
            if not isinstance(v, Pair):
                raise TableError(f"pc {pc}: unpack of a value that is not a pair ({v})")
            return {dests[0]: v.lo, dests[1]: v.hi}
        if head == "mov":
            text, regs = srcs[0]
            if len(regs) == 2 and None not in regs:
                lo, hi = (self.value(env, r, pc) for r in regs)
                if isinstance(lo, Opaque) or isinstance(hi, Opaque):
                    raise TableError(f"pc {pc}: pack of values of unknown shape")
                return {dests[0]: Pair(lo, hi)}
            return {dests[0]: src(0)}
        if head in ("add", "sub", "mul", "fma") and last == "f32":
            if head == "sub" and rounding not in (None, "rn"):
                raise TableError(f"pc {pc}: {opcode} has no ideal-real rule")
            x = [paren(r) for r in reals("f32", 3 if head == "fma" else 2)]
            return {dests[0]: Float("f32", ARITH[head](x))}
        if head in ("add", "sub", "mul", "fma") and last == "f32x2":
            if head != "mul" and rounding not in (None, "rn"):
                raise TableError(f"pc {pc}: {opcode} has no ideal-real rule (directed rounding)")
            ps = pairs(3 if head == "fma" else 2)
            lo, hi = (Float("f32", ARITH[head]([paren(p[k]) for p in ps])) for k in range(2))
            return {dests[0]: Pair(lo, hi)}
        if head in ("max", "min") and last == "f32":
            x = [paren(r) for r in reals("f32", len(srcs))]
            expr = f"{head} {x[0]} {x[1]}"
            if len(x) == 3:
                expr = f"{head} ({expr}) {x[2]}"
            return {dests[0]: Float("f32", expr)}
        if opcode.startswith("cvt.rn.f16x2.f32"):
            a, b = reals("f32", 2)
            return {dests[0]: Pair(Float("f16", b), Float("f16", a))}
        if head == "cvt" and mods[:2] == ["f32", "f16"]:
            (a,) = reals("f16", 1)
            return {dests[0]: Float("f32", a)}
        if head == "setp" and last == "f32" and mods[0] in CMP:
            a, b = reals("f32", 2)
            term = f"Assumption.realCompare .{CMP[mods[0]]} {paren(a)} {paren(b)}"
            return {dests[0]: Pred(term)}
        raise TableError(f"pc {pc}: no template for {opcode} {', '.join(ins['operands'])}")

    def walk(self, start: int, end: int, env: dict, preds: dict, limit: int = 100000):
        written = {}
        pc = start
        steps = 0
        while pc != end:
            if pc >= len(self.code) or steps > limit:
                raise TableError(f"no path from {start} to {end}")
            ins = self.code[pc]
            if ins["event"]:
                raise TableError(f"pc {pc}: event instruction {ins['opcode']} inside the segment")
            steps += 1
            guard = ins["guard"]
            taken = True
            if guard is not None:
                name = guard["register"]
                if name not in preds:
                    raise TableError(f"pc {pc}: guard {name} not given (--pred {name}=true)")
                taken = preds[name] != guard["negated"]
            if ins["opcode"].split(".")[0] == "bra":
                pc = ins["target"] if taken else pc + 1
                continue
            if taken:
                for reg, v in self.step(ins, env, preds).items():
                    env[reg] = v
                    written[reg] = v
            pc += 1
        return written


def paren(s: str) -> str:
    return s if re.fullmatch(r"[\w.']+", s) else f"({s})"


# The ideal-real results (ASM-IDEAL `execIdealFloat`), operands in code order.
ARITH = {
    "add": lambda x: f"{x[0]} + {x[1]}",
    "sub": lambda x: f"{x[0]} - {x[1]}",
    "mul": lambda x: f"{x[0]} * {x[1]}",
    "fma": lambda x: f"{x[0]} * {x[1]} + {x[2]}",
}


def generate(
    ptx: Path,
    start: str,
    end: str,
    inputs: dict,
    preds: dict,
    templates: dict,
    all_written: bool = False,
) -> str:
    w = Walker(ptx, templates)
    s = w.pc_of(start, after_site=True)
    e = w.pc_of(end, after_site=False)
    env = {r: parse_value(v, r) for r, v in inputs.items()}
    written = w.walk(s, e, dict(env), preds)
    live = w.live(e) if e < len(w.code) else set()
    regs = sorted((r for r in written if all_written or r in live), key=lambda r: w.ids.get(r, -1))
    lines = []
    for r in regs:
        if r not in w.ids:
            raise TableError(f"register {r} has no id")
        lines.append(f"  ({w.ids[r]}, {written[r].lean()}),  -- {r}")
    return "\n".join(lines) + ("\n" if lines else "")


def parse_preds(items):
    out = {}
    for item in items or []:
        name, _, value = item.partition("=")
        if value not in ("true", "false"):
            raise TableError(f"--pred {item}: expected NAME=true or NAME=false")
        out[name] = value == "true"
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("ptx", type=Path)
    parser.add_argument("--start", required=True, help="site (segment starts after it) or pc:N")
    parser.add_argument("--end", required=True, help="site or pc:N (not included)")
    parser.add_argument("--inputs", type=Path, required=True, help="JSON start values")
    parser.add_argument("--pred", action="append", help="NAME=true|false for guards/branches")
    parser.add_argument("--templates", type=Path, help="JSON results of further opcodes")
    parser.add_argument("--all", action="store_true", help="also dead written registers")
    args = parser.parse_args(argv)
    try:
        text = generate(
            args.ptx,
            args.start,
            args.end,
            json.loads(args.inputs.read_text()),
            parse_preds(args.pred),
            json.loads(args.templates.read_text()) if args.templates else {},
            args.all,
        )
    except TableError as err:
        print(f"value_table: {err}", file=sys.stderr)
        return 1
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
