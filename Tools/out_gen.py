# SPDX-License-Identifier: Apache-2.0
"""Straight-line runs of local instructions as pieces with stated values, generated from the PTX.

A run of local instructions (moves, packed and scalar floating instructions, and instructions a
role reads by its own outcome function) is proved by `SegD.outs_lit`
(`Lemmas/Flow/OutLit.lean`) piece by piece. For each piece this generator writes the items, the
facts at the piece's end with each register's value as the literal term the code computes (a
`def` per written register, in terms of the values `V` at the start of the run), and the proof:
item by item the code lemma `Flow.code_<pc>` and the role's segment and reading lemmas the
declaration names, Boolean checks by `rfl`, and the stated values by `kernel_rfl`. The run
theorem composes the pieces. No proof searches: every lemma is named and every check evaluates
literals.

It reads only the PTX (instruction order and register ids as `Tools/flow_gen.py` and
`Core/Source/Decode.lean` compute them) and a declaration (JSON):

    {"ptx": "Kernels/K/k.ptx", "namespace": "PTX.Kernels.K.Gen", "output": "Kernels/K/Gen.lean",
     "imports": ["Kernels.K.Flow.Code", "Kernels.K.Rules"],
     "kernel": "PTX.Kernels.K.Decoded.kernel", "code": "PTX.Kernels.K.Flow",
     "assumptions": "PTX.Kernels.K.Assumptions.all",
     "runs": [{"name": "expo", "start": 4399, "end": 4826, "cut": 32,
               "outputs": ["%r2819", "%r2820"],
               "segfree": "R.segFree {pc} rfl",
               "rules": {"mul": "R.rule_mul {pc} rfl", "pack": "R.rule_move {pc}", ...},
               "fn": {"cvt.rn.bf16x2.f32": {"op": "R.cvtOp", "f": "R.packE"}}}]}

`outputs` are the registers the facts at the end state (with registers the run does not write
passed through from the start). `rules` gives, per item kind (`mul`, `add`, `sub`, `fma2`, `add2`,
`ex2`, `max2`/`max3` (`max.f32` of two or three sources), `pack`, `unpack`, `mov`, `fn`), a term of
type `∀ s : TState, s.pc = <pc> → it.Rule A L g s` with `{pc}` for the item's pc. `fn` declares an opcode read by a role's outcome function `f` on the
values of its sources, with `op d [srcs]` its instruction. An instruction outside these kinds, a
branch, an event or a guarded instruction stops the generator.

An optional `"options": {"maxRecDepth": 100000}` sets Lean options for the generated file (a
reading whose `rfl` side condition evaluates a long site list needs a deeper recursion).

    python Tools/out_gen.py decl.json            # write the output
    python Tools/out_gen.py decl.json --check    # fail if the output is stale
"""

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402
from lean_wrap import wrap_lines  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

SCALAR = {
    "mul.f32": ("mul", "false"),
    "mul.ftz.f32": ("mul", "true"),
    "mul.rn.f32": ("mul", "false"),
    "sub.f32": ("sub", "false"),
    "sub.ftz.f32": ("sub", "true"),
    "add.f32": ("add", "false"),
    "add.ftz.f32": ("add", "true"),
}
SCALAR_E = {
    "mul": "mulE {fz} ({a}) ({b})",
    "sub": "subE {fz} ({a}) ({b})",
    "add": "floatE (addI {fz}) [{a}, {b}]",
}


class GenError(Exception):
    pass


def regs_of(text):
    return [r.strip() for r in text.strip("{}").split(",")]


class Run:
    def __init__(self, code, ids, run):
        self.code, self.ids, self.run = code, ids, run
        self.name = run["name"]
        self.fn = run.get("fn", {})

    def rid(self, reg):
        if reg not in self.ids:
            raise GenError(f"unknown register {reg}")
        return self.ids[reg]

    def item(self, ins):
        """(kind, item term, reads, writes, value builder) of an instruction."""
        op, ops, pc = ins["opcode"], ins["operands"], ins["pc"]
        if ins["guard"] or ins["event"] or ins["target"] is not None:
            raise GenError(f"pc {pc}: {op} is not an unguarded local instruction")
        r = self.rid
        if op in self.fn:
            d, srcs = r(ops[0]), [r(x) for x in ops[1:]]
            spec = self.fn[op]
            sl = "[" + ", ".join(map(str, srcs)) + "]"
            term = f".fn ({spec['op']} {d} {sl}) {d} {sl} {spec['f']}"
            return (
                "fn",
                term,
                srcs,
                [d],
                lambda v: [
                    (d, f"okVal (.bits 32 0) ({spec['f']} [{', '.join(v(s) for s in srcs)}])")
                ],
            )
        if op == "max.f32" and len(ops) in (3, 4):
            # `max.f32` of two or three register sources: a `fn` item with the library's outcome
            # `maxE` (`XItem.max2_rule`, `XItem.max3_rule`)
            d, srcs = r(ops[0]), [r(x) for x in ops[1:]]
            sl = "[" + ", ".join(map(str, srcs)) + "]"
            return (
                f"max{len(srcs)}",
                f".fn (maxOp {d} {sl}) {d} {sl} maxE",
                srcs,
                [d],
                lambda v: [(d, f"okVal (.bits 32 0) (maxE [{', '.join(v(x) for x in srcs)}])")],
            )
        if op in SCALAR:
            kind, fz = SCALAR[op]
            d, a, b = r(ops[0]), r(ops[1]), r(ops[2])
            e = SCALAR_E[kind]
            return (
                kind,
                f".{kind} {fz} {d} {a} {b}",
                [a, b],
                [d],
                lambda v: [(d, "okVal (.bits 32 0) (" + e.format(fz=fz, a=v(a), b=v(b)) + ")")],
            )
        if op == "fma.rn.f32x2":
            d, a, b, c = (r(x) for x in ops)
            return (
                "fma2",
                f".fma2 {d} {a} {b} {c}",
                [a, b, c],
                [d],
                lambda v: [(d, f"okVal (.bits 64 0) (fma2E ({v(a)}) ({v(b)}) ({v(c)}))")],
            )
        if op == "add.rn.f32x2":
            d, a, b = (r(x) for x in ops)
            return (
                "add2",
                f".add2 {d} {a} {b}",
                [a, b],
                [d],
                lambda v: [(d, f"okVal (.bits 64 0) (add2E ({v(a)}) ({v(b)}))")],
            )
        if op in ("ex2.approx.f32", "ex2.approx.ftz.f32"):
            fz = "true" if "ftz" in op else "false"
            d, a = r(ops[0]), r(ops[1])
            return (
                "ex2",
                f".ex2 {fz} {d} {a}",
                [a],
                [d],
                lambda v: [(d, f"okVal (.bits 32 0) (ex2E {fz} ({v(a)}))")],
            )
        if op == "mov.b64" and ops[1].startswith("{"):
            (a, b), d = [r(x) for x in regs_of(ops[1])], r(ops[0])
            return (
                "pack",
                f".pack {d} {a} {b}",
                [a, b],
                [d],
                lambda v: [(d, f"joinValue ({v(a)}) ({v(b)})")],
            )
        if op == "mov.b64" and ops[0].startswith("{"):
            (lo, hi), a = [r(x) for x in regs_of(ops[0])], r(ops[1])
            return (
                "unpack",
                f".unpack {lo} {hi} {a}",
                [a],
                [lo, hi],
                lambda v: [
                    (lo, f"(splitValue 64 ({v(a)})).1"),
                    (hi, f"(splitValue 64 ({v(a)})).2"),
                ],
            )
        if op in ("mov.b32", "mov.f32", "mov.u32") and ops[1].startswith("%"):
            d, a = r(ops[0]), r(ops[1])
            return ("mov", f".mov {d} {a}", [a], [d], lambda v: [(d, v(a))])
        raise GenError(f'pc {pc}: {op} has no item; declare it under "fn"')

    def render(self, kernel, codens, asms):
        run = self.run
        start, end, cut = run["start"], run["end"], run.get("cut", 32)
        items = [self.item(self.code[pc]) for pc in range(start, end)]
        outputs = [self.rid(x) for x in run.get("outputs", [])]
        n = len(items)
        # live registers before item i: read later before written, or an output not written later
        live = [None] * (n + 1)
        cur = set(outputs)
        live[n] = sorted(cur)
        for i in range(n - 1, -1, -1):
            _, _, rd, wr, _ = items[i]
            cur = (cur - set(wr)) | set(rd)
            live[i] = sorted(cur)
        bounds = list(range(0, n, cut)) + [n]
        name = self.name
        out = []

        def dname(pc, k, wr):
            return f"{name}_v{pc}" + (f"_{k}" if len(wr) > 1 else "")

        # one def per written register, in terms of the defs before it and the start values `V`
        defs, cur, at_bound = [], {}, {0: {}}

        def v(rr):
            return f"{cur[rr]} V" if rr in cur else f"V {rr}"

        for i, (kind, term, rd, wr, vals) in enumerate(items):
            pc = start + i
            for k, (d, t) in enumerate(vals(v)):
                defs += [f"def {dname(pc, k, wr)} (V : Nat → Value) : Value :=", f"  {t}"]
            for k, d in enumerate(wr):
                cur[d] = dname(pc, k, wr)
            items[i] = (kind, term, rd, wr, pc)
            if i + 1 in bounds:
                at_bound[i + 1] = dict(cur)

        def facts(i):
            m = at_bound[i]
            return [f"({rr}, {m[rr] + ' V' if rr in m else f'V {rr}'})" for rr in live[i]]

        out.append(f"/-! ## `{name}`: pcs {start}–{end - 1} -/")
        out.append("")
        out += defs
        out.append("")
        for j, b in enumerate(bounds):
            fl = facts(b)
            out.append(f"/-- The facts at pc {start + b}. -/")
            out.append(f"def {name}_facts{j} (V : Nat → Value) : List (Nat × Value) := [")
            out += [f"  {x}," for x in fl[:-1]] + ([f"  {fl[-1]}"] if fl else [])
            out.append("]")
            out.append("")
        segfree, rules = run["segfree"], run["rules"]
        pieces = []
        for j in range(len(bounds) - 1):
            a, b = bounds[j], bounds[j + 1]
            its = items[a:b]
            out.append(f"def {name}_items{j} : List XItem := [")
            terms = [t if k in ("fn", "max2", "max3") else f".base ({t})" for k, t, _, _, _ in its]
            out += [f"  {t}," for t in terms[:-1]] + [f"  {terms[-1]}"]
            out.append("]")
            out.append("")
            pa, pb = start + a, start + b
            cond = f"xCond (lookupD ({name}_facts{j} V)) {name}_items{j}"
            pieces.append((j, pa, pb, b - a, cond))
            out.append(f"theorem {name}_piece{j} (L : Launch) (g : Nat) (V : Nat → Value) :")
            out.append(f"    SegD {kernel} {asms} L g {b - a} {pa} ({name}_facts{j} V) {pb}")
            out.append(f"      ({name}_facts{j + 1} V) ({cond}) :=")
            out.append(f"  SegD.outs_lit (items := {name}_items{j})")
            ats = []
            for kind, _, _, _, pc in its:
                rule = rules.get(kind)
                if rule is None:
                    raise GenError(f"pc {pc}: no rule declared for the item kind {kind}")
                ats.append(
                    f"⟨XItem.codeB_of {codens}.code_{pc} rfl, {segfree.format(pc=pc)}, "
                    f"{rule.format(pc=pc)}⟩"
                )
            out.append("    ⟨" + ats[0] + ",")
            out += [f"     {x}," for x in ats[1:]]
            out.append("     trivial⟩")
            out.append("    rfl (by kernel_rfl) rfl (by kernel_rfl) (by kernel_rfl)")
            out.append("")
        conj = pieces[0][4]
        proof = f"{name}_piece0 L g V"
        total = pieces[0][3]
        for j, _, _, ln, cond in pieces[1:]:
            conj = f"({conj}) ∧ ({cond})"
            proof = f"({proof}).comp ({name}_piece{j} L g V)"
            total += ln
        out.append(f"/-- The condition of `{name}`: each piece's outcomes are no fault. -/")
        out.append(f"def {name}_cond (V : Nat → Value) : Prop :=")
        out.append(f"  {conj}")
        out.append("")
        out.append(f"theorem {name}_run (L : Launch) (g : Nat) (V : Nat → Value) :")
        out.append(f"    SegD {kernel} {asms} L g {total} {start} ({name}_facts0 V) {end}")
        out.append(f"      ({name}_facts{len(bounds) - 1} V) ({name}_cond V) :=")
        out.append(f"  {proof}")
        out.append("")
        return out


def render(decl):
    ptx = ROOT / decl["ptx"]
    program = parse_ptx.parse(ptx.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        f"-- Generated by Tools/out_gen.py from {decl['ptx']}; do not edit.",
        "module",
        "",
        *[
            f"public import {m}"
            for m in ["Lemmas.Flow.OutLit", "Tactics.KernelRfl", *decl.get("imports", [])]
        ],
        "",
        "@[expose] public section",
        "",
        f"namespace {decl['namespace']}",
        "open PTX PTX.Flow PTX.Proof PTX.Assumption",
        "",
        "noncomputable section",
        *[f"set_option {k} {v}" for k, v in decl.get("options", {}).items()],
        "",
    ]
    for run in decl["runs"]:
        lines += Run(code, ids, run).render(decl["kernel"], decl["code"], decl["assumptions"])
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
        sys.exit(f"out_gen: {e}")
    out = ROOT / decl["output"]
    if args.check:
        if not out.exists() or out.read_text() != text:
            sys.exit(f"out_gen: {decl['output']} is stale; rerun Tools/out_gen.py")
        return
    out.write_text(text)


if __name__ == "__main__":
    main()
