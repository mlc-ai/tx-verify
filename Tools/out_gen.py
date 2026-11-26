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
`ex2`, `max2`/`max3` (`max.f32` of two or three sources), `setp` (`setp.<cmp>{.ftz}.f32 p, a, 0f…`),
`pack`, `unpack`, `mov`, `sink` (`mov.b<w> {d, _}` or `{_, d}`, `XItem.core_sink`), `fn`), a term of
type `∀ s : TState, s.pc = <pc> → it.Rule A L g s` with `{pc}` for the item's pc. `fn` declares an opcode read by a role's outcome function `f` on the
values of its sources, with `op d [srcs]` its instruction. An instruction outside these kinds, a
branch, an event or a guarded instruction stops the generator.

Operands: a register (also a block-scoped one of the PTX), an integer immediate or a `0f`
constant. A `fn` declaration whose `op` or `f` contains `{` is a format over `{d}`, `{srcs}` (the
source registers as a Lean list) and `{o1}`, `{o2}`, … (the operands after the destination, as
`Opnd` terms), so an opcode with immediates (the `.ftz` scalar forms of a software exponent) is
declared by the kernel; `rule` in a `fn` declaration overrides `rules["fn"]` for that opcode.
`selp.f32` (with register or literal sources) and `mov.b32 d, 0f…` are the library items
`selp` and `movImm`.

Core's forms (`Lemmas/Flow/OutCore.lean`): with a `"decoded"` path (the kernel's
`Data/Decoded.lean`) in the declaration, an integer `setp` without a combining predicate,
`add`/`sub` of a scalar integer type, `shl`, `shr`, `and`/`or`, `mov` of a predicate or a
literal, `mov.b128 d, {a, b}`, an integer-to-integer `cvt` and `cvt.f32.bf16` are `fn` items with
Core's value (`coreF`); each instruction's decoded term is one `def <run>_op<pc>`, which the item
and its value share. Their rule is `rules["core"]`, a format with `{lemma}` (the form's rule
lemma `XItem.core_<form>`) and `{checks}` (the lemma's `rfl` checks), e.g.
`"{lemma} (R.segFree {pc} rfl) (R.noRule{cls} {pc}) {checks}"`, with `{cls}` the family of the
instruction (`Int`, `Move` or `Cvt`); `{op}` names the instruction's `def`.

A `fn` declaration keyed `"<opcode>@<pc>"` applies at that pc only, before the opcode's
(an opcode with two operand orders at different sites). With `"out"` (a Lean term in `{V}`) a
run also gets `<run>_out` (its last facts are that term, by `rfl`) and `<run>_seg` (the run as a
`Seg` under its condition, to those facts). A source path that makes the generated-file comment
longer than the line width is written on a line of its own.

A declaration with `"template"` is a run family's instances (`Tools/out_family.py`): one copy
of a handwritten Lean template per generated run of the same shape, with its names substituted.

An optional `"options": {"maxRecDepth": 100000}` sets Lean options for the generated file (a
reading whose `rfl` side condition evaluates a long site list needs a deeper recursion).

Forms beyond the fixed kinds are declared under `fn`, keyed by the opcode or by the opcode and
the shape of its sources:

* `"<opcode>"`: every source is a register (`cvt.rn.bf16.f32`, `fma.rn.ftz.f32`);
* `"<opcode>#imm"`: the last source is a constant (`mul.ftz.f32 d, a, 0f…`, `shl.b32 d, a, 16`);
  its item is `.fn (op k d [srcs]) d [srcs] (f k)` with `k` the constant (the bits of a `0f…`
  constant as a natural number, an integer otherwise);
* `"<opcode>#pack"`: the source is a vector `{lo, hi}` (`mov.b32 d, {lo, hi}`), read as the two
  registers.

An `fn` entry may name its item kind (`"kind"`, for the comments of the declaration only) and
its reading lemma (`"rule"`, with `{pc}`); without `"rule"` the run's `rules["fn"]` is used.

`mov.b32 {lo, hi}, a` (the kind `unpack32`) writes two registers and is no run item: the
generator cuts the run before and after it and proves it as a piece of its own with the lemma
`rules["unpack32"]` (of the form of `SegD.outs_lit` for one instruction: the code lemma, then
Boolean checks by `rfl` and the stated values by `kernel_rfl`); its condition is that the value
unpacks (`∃ x, unpackE 32 … = .ok x`).

    python Tools/out_gen.py decl.json            # write the output
    python Tools/out_gen.py decl.json --check    # fail if the output is stale
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


INT_TYPES = ("s16", "u16", "s32", "u32", "s64", "u64", "b16", "b32", "b64")
SETP_CMP = ("eq", "ne", "lt", "le", "gt", "ge", "lo", "ls", "hi", "hs")


def core_form(op, ops):
    """(rule lemma, checks) of Core's forms (`Lemmas/Flow/OutCore.lean`), or None."""
    parts = op.split(".")
    head = parts[0]
    if head == "setp" and len(parts) == 3 and parts[1] in SETP_CMP and parts[2] in INT_TYPES:
        if len(ops) == 3:
            return "core_setp", "rfl"
    if head in ("add", "sub") and len(parts) == 2 and parts[1] in INT_TYPES and len(ops) == 3:
        return f"core_{head}", "rfl"
    if head in ("shl", "shr") and len(parts) == 2 and parts[1] in INT_TYPES and len(ops) == 3:
        return f"core_{head}", "rfl"
    if head in ("and", "or") and len(parts) == 2 and (parts[1] in INT_TYPES or parts[1] == "pred"):
        if len(ops) == 3:
            return f"core_{head}", "rfl"
    if op.startswith("mul.lo.") and len(parts) == 3 and parts[2] in INT_TYPES and len(ops) == 3:
        return "core_mulLo", "rfl"
    if op == "prmt.b32" and len(ops) == 4:
        return "core_prmt", "rfl"
    if head == "selp" and len(parts) == 2 and parts[1] in INT_TYPES and len(ops) == 4:
        return "core_selp", "rfl"
    if op == "mov.pred" and len(ops) == 2:
        return "core_mov", "rfl"
    if head == "mov" and len(parts) == 2 and parts[1] in INT_TYPES and len(ops) == 2:
        try:
            int(ops[1][:-1] if ops[1][-1:] in "uU" else ops[1], 0)
            return "core_mov", "rfl"
        except ValueError:
            pass
    if op == "mov.b128" and len(ops) == 2 and ops[1].startswith("{") and len(regs_of(ops[1])) == 2:
        return "core_pack", "rfl"
    cvt_types = (*INT_TYPES, "s8", "u8", "b8")
    if head == "cvt" and len(parts) == 3 and parts[1] in cvt_types and parts[2] in cvt_types:
        return "core_cvtInt", "rfl rfl rfl rfl"
    if op == "cvt.f32.bf16":
        return "core_cvtFloat", "rfl rfl rfl rfl"
    return None


def decoded_ops(path):
    """The decoded operation term of each pc (`{ guard := …, op := <term> }`)."""
    from code_table import items

    out = []
    for it in items(path.read_text()):
        body = " ".join(it.split())
        if not body.startswith("{ guard := none, op := ") or not body.endswith("}"):
            out.append(None)
            continue
        out.append(body[len("{ guard := none, op := ") : -1].strip())
    return out


def regs_of(text):
    return [r.strip() for r in text.strip("{}").split(",")]


class Run:
    def __init__(self, code, ids, run):
        self.code, self.ids, self.run = code, ids, run
        self.name = run["name"]
        self.fn = run.get("fn", {})
        self.ops = None
        self.opdefs = []
        self.fn_rules = {}

    def opnd(self, x):
        """The `Opnd` term of an operand: a register, an integer immediate or a `0f` constant."""
        if x in self.ids:
            return f".reg {self.ids[x]}"
        if x.startswith(("0f", "0F")):
            return f".f32imm {int(x[2:], 16)}"
        try:
            return f".imm ({int(x[:-1] if x[-1:] in 'uU' else x, 0)})"
        except ValueError:
            raise GenError(f"operand {x} is not a register or a literal") from None

    def is_reg(self, x):
        return x in self.ids

    def rid(self, reg):
        if reg not in self.ids:
            raise GenError(f"unknown register {reg}")
        return self.ids[reg]

    def fn_kind(self, spec, pc):
        """The kind of an `fn` item: `fn`, or a kind of its own when the entry names its rule."""
        if "rule" not in spec:
            return "fn"
        kind = "fn:" + spec.get("kind", spec["f"])
        self.fn_rules[kind] = spec["rule"]
        return kind

    def shaped(self, op, ops):
        """The item of a form declared under `fn` by opcode and source shape, or of `unpack32`."""
        r = self.rid
        if op == "mov.b32" and ops[0].startswith("{") and "_" not in regs_of(ops[0]):
            (lo, hi), a = [r(x) for x in regs_of(ops[0])], r(ops[1])
            return (
                "unpack32",
                (lo, hi, a),
                [a],
                [lo, hi],
                lambda v: [
                    (lo, f"(splitValue 32 ({v(a)})).1"),
                    (hi, f"(splitValue 32 ({v(a)})).2"),
                ],
            )
        if len(ops) == 2 and ops[1].startswith("{") and op + "#pack" in self.fn:
            spec = self.fn[op + "#pack"]
            d, srcs = r(ops[0]), [r(x) for x in regs_of(ops[1])]
            sl = "[" + ", ".join(map(str, srcs)) + "]"
            return (
                self.fn_kind(spec, None),
                f".fn ({spec['op']} {d} {sl}) {d} {sl} {spec['f']}",
                srcs,
                [d],
                lambda v: [
                    (d, f"okVal (.bits 32 0) ({spec['f']} [{', '.join(v(s) for s in srcs)}])")
                ],
            )
        if len(ops) >= 2 and not ops[-1].startswith(("%", "{")) and op + "#imm" in self.fn:
            spec = self.fn[op + "#imm"]
            d, srcs = r(ops[0]), [r(x) for x in ops[1:-1]]
            k = ops[-1]
            k = str(int(k[2:], 16)) if k.startswith("0f") else (k if int(k) >= 0 else f"({k})")
            sl = "[" + ", ".join(map(str, srcs)) + "]"
            return (
                self.fn_kind(spec, None),
                f".fn ({spec['op']} {k} {d} {sl}) {d} {sl} ({spec['f']} {k})",
                srcs,
                [d],
                lambda v: [
                    (d, f"okVal (.bits 32 0) ({spec['f']} {k} [{', '.join(v(s) for s in srcs)}])")
                ],
            )
        return None

    def item(self, ins):
        """(kind, item term, reads, writes, value builder) of an instruction."""
        op, ops, pc = ins["opcode"], ins.get("resolved", ins["operands"]), ins["pc"]
        if ins["guard"] or ins["event"] or ins["target"] is not None:
            raise GenError(f"pc {pc}: {op} is not an unguarded local instruction")
        r = self.rid
        shaped = self.shaped(op, ops)
        if shaped is not None:
            return shaped
        key = f"{op}@{pc}" if f"{op}@{pc}" in self.fn else op
        if key in self.fn:
            spec = self.fn[key]
            d = r(ops[0])
            if "{" in spec["op"] or "{" in spec["f"]:
                srcs = [r(x) for x in ops[1:] if self.is_reg(x)]
                sl = "[" + ", ".join(map(str, srcs)) + "]"
                fmt = {"d": d, "srcs": sl}
                fmt.update({f"o{k}": f"({self.opnd(x)})" for k, x in enumerate(ops[1:], 1)})
                fop, ff = spec["op"].format(**fmt), spec["f"].format(**fmt)
                term = f".fn ({fop}) {d} {sl} ({ff})"
                return (
                    self.fn_kind(spec, pc),
                    term,
                    srcs,
                    [d],
                    lambda v: [
                        (d, f"okVal (.bits 32 0) (({ff}) [{', '.join(v(x) for x in srcs)}])")
                    ],
                )
            srcs = [r(x) for x in ops[1:]]
            sl = "[" + ", ".join(map(str, srcs)) + "]"
            term = f".fn ({spec['op']} {d} {sl}) {d} {sl} {spec['f']}"
            return (
                self.fn_kind(spec, pc),
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
        m = re.fullmatch(r"setp\.(eq|ne|lt|le|gt|ge)(\.ftz)?\.f32", op)
        if m and len(ops) == 3 and self.is_reg(ops[1]) and ops[2].startswith(("0f", "0F")):
            # `setp.<cmp>{.ftz}.f32 p, a, 0f…`: the library item `setp` (ordered comparison)
            fz = "true" if m.group(2) else "false"
            p, a, k = r(ops[0]), r(ops[1]), int(ops[2][2:], 16)
            c = f"(.ord .{m.group(1)})"
            return (
                "setp",
                f".setp {c} {fz} {p} {a} {k}",
                [a],
                [p],
                lambda v: [
                    (
                        p,
                        f".pred (okPred (setpE {c} {fz} ({v(a)}) "
                        f"(.bits 32 (BitVec.ofNat 64 {k}))))",
                    )
                ],
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
        sink = [x.strip() for x in ops[0].strip("{}").split(",")] if ops[0].startswith("{") else []
        if op in ("mov.b32", "mov.b64") and len(sink) == 2 and sink.count("_") == 1:
            # `mov.b<w> {d, _}, a` / `{_, d}, a`: Core's unpack keeping one half
            # (`XItem.core_sink`, rule `rules["sink"]`)
            w, lo = op[-2:], "true" if sink[1] == "_" else "false"
            d, a = r(sink[0] if lo == "true" else sink[1]), r(ops[1])
            f = f"(fun vs => sinkW {w} {lo} {a} (lk [{a}] vs))"
            return (
                "sink",
                f".fn (sinkOp {w} {lo} {d} {a}) {d} [{a}] {f}",
                [a],
                [d],
                lambda v: [(d, f"okVal (.bits 32 0) ({f} [{v(a)}])")],
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
        if op in ("mov.b32", "mov.f32", "mov.u32") and self.is_reg(ops[1]):
            d, a = r(ops[0]), r(ops[1])
            return ("mov", f".mov {d} {a}", [a], [d], lambda v: [(d, v(a))])
        if op in ("mov.b32", "mov.f32") and ops[1].startswith(("0f", "0F")):
            d, b = r(ops[0]), int(ops[1][2:], 16)
            return (
                "movImm",
                f".movImm {d} {b}",
                [],
                [d],
                lambda v: [(d, f"(.bits 32 (BitVec.ofNat 64 {b}))")],
            )
        if op == "selp.f32" and len(ops) == 4 and self.is_reg(ops[3]):
            d, p = r(ops[0]), r(ops[3])
            a, b = self.opnd(ops[1]), self.opnd(ops[2])
            rd = [r(x) for x in ops[1:3] if self.is_reg(x)] + [p]

            def sv(v, x, t):
                return v(r(x)) if self.is_reg(x) else f"opndVal V ({t})"

            return (
                "selp",
                f".selp {d} ({a}) ({b}) {p}",
                rd,
                [d],
                lambda v: [
                    (d, f"if predOf ({v(p)}) then {sv(v, ops[1], a)} else {sv(v, ops[2], b)}")
                ],
            )
        form = core_form(op, ops)
        if form is not None and self.ops is not None:
            return self.core_item(pc, op, ops, form)
        raise GenError(f'pc {pc}: {op} has no item; declare it under "fn"')

    def core_item(self, pc, op, ops, form):
        r = self.rid
        term = self.ops[pc] if pc < len(self.ops) else None
        if term is None:
            raise GenError(f"pc {pc}: {op} has no decoded unguarded instruction")
        lemma, checks = form
        name = f"{self.name}_op{pc}"
        self.opdefs += [f"def {name} : Op :=", f"  {term}"]
        if ops[1].startswith("{"):
            srcs = [r(x) for x in regs_of(ops[1])]
        else:
            srcs = [r(x) for x in ops[1:] if self.is_reg(x)]
        d = r(ops[0])
        sl = "[" + ", ".join(map(str, srcs)) + "]"
        return (
            ("core", lemma, checks),
            f".fn {name} {d} {sl} (coreF {name} {sl})",
            srcs,
            [d],
            lambda v: [
                (d, f"okVal (.bits 32 0) (coreF {name} {sl} [{', '.join(v(x) for x in srcs)}])")
            ],
        )

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
        singles = [i for i, it in enumerate(items) if it[0] == "unpack32"]
        if singles:
            # an unpack is a piece of its own; the stretches between unpacks are cut every `cut`
            marks, last = {0, n}, 0
            for i in singles + [n]:
                marks.update(range(last, i, cut))
                marks.update({i, min(i + 1, n)})
                last = i + 1
            bounds = sorted(marks)
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
                vb = "V" if re.search(r"\bV\b", t) else "_V"
                defs += [f"def {dname(pc, k, wr)} ({vb} : Nat → Value) : Value :=", f"  {t}"]
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
        out += self.opdefs
        out += defs
        out.append("")
        for j, b in enumerate(bounds):
            fl = facts(b)
            out.append(f"/-- The facts at pc {start + b}. -/")
            vb = "V" if any(re.search(r"\bV\b", x) for x in fl) else "_V"
            out.append(f"def {name}_facts{j} ({vb} : Nat → Value) : List (Nat × Value) := [")
            out += [f"  {x}," for x in fl[:-1]] + ([f"  {fl[-1]}"] if fl else [])
            out.append("]")
            out.append("")
        segfree, rules = run["segfree"], run["rules"]
        pieces = []
        for j in range(len(bounds) - 1):
            a, b = bounds[j], bounds[j + 1]
            its = items[a:b]
            if its[0][0] == "unpack32":
                (_, (lo, hi, src), _, _, pc) = its[0]
                rule = rules.get("unpack32")
                if rule is None:
                    raise GenError(f"pc {pc}: no rule declared for the item kind unpack32")
                cond = f"∃ x, unpackE 32 (lookupD ({name}_facts{j} V) {src}) = .ok x"
                pieces.append((j, pc, pc + 1, 1, cond))
                out.append(f"theorem {name}_piece{j} (L : Launch) (g : Nat) (V : Nat → Value) :")
                out.append(f"    SegD {kernel} {asms} L g 1 {pc} ({name}_facts{j} V) {pc + 1}")
                out.append(f"      ({name}_facts{j + 1} V) ({cond}) :=")
                out.append(f"  {rule.format(pc=pc)} (lo := {lo}) (hi := {hi}) (a := {src})")
                out.append(f"    {codens}.code_{pc} rfl rfl (by kernel_rfl) (by kernel_rfl)")
                out.append("")
                continue
            out.append(f"def {name}_items{j} : List XItem := [")
            terms = [t if t.startswith(".fn ") else f".base ({t})" for _, t, _, _, _ in its]
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
                if isinstance(kind, tuple):
                    rule = rules.get("core")
                    if rule is None:
                        raise GenError(f"pc {pc}: no rule declared for the item kind core")
                    cls = {"core_mov": "Move", "core_pack": "Move"}.get(kind[1], "Int")
                    cls = "Cvt" if kind[1].startswith("core_cvt") else cls
                    rule = rule.format(
                        pc=pc,
                        lemma=f"PTX.Flow.XItem.{kind[1]}",
                        checks=kind[2],
                        cls=cls,
                        op=f"{name}_op{pc}",
                    )
                else:
                    rule = self.fn_rules.get(kind) or rules.get(kind)
                    if rule is None:
                        raise GenError(f"pc {pc}: no rule declared for the item kind {kind}")
                    rule = rule.format(pc=pc)
                ats.append(
                    f"⟨XItem.codeB_of {codens}.code_{pc} rfl, {segfree.format(pc=pc)}, {rule}⟩"
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
        if "out" in run:
            last = len(bounds) - 1
            out.append(f"/-- The facts at the end of `{name}`, in the role's form. -/")
            out.append(f"theorem {name}_out (V : Nat → Value) :")
            out.append(f"    {name}_facts{last} V = {run['out'].format(V='V')} := rfl")
            out.append("")
            out.append(f"/-- **`{name}`** under its condition, to the facts in the role's form. -/")
            out.append(f"theorem {name}_seg (L : Launch) (g : Nat) (V : Nat → Value)")
            out.append(f"    (hc : {name}_cond V) :")
            out.append(f"    Seg {kernel} {asms} L g {total} {start} ({name}_facts0 V) {end}")
            out.append(f"      ({run['out'].format(V='V')}) :=")
            out.append(f"  {name}_out V ▸ ({name}_run L g V).seg hc")
            out.append("")
        return out


def header(ptx):
    """The generated-file comment, on two lines when one exceeds the line width."""
    line = f"-- Generated by Tools/out_gen.py from {ptx}; do not edit."
    if len(line) <= 100:
        return [line]
    return ["-- Generated by Tools/out_gen.py; do not edit.", f"-- Source: {ptx}"]


def render(decl):
    if "template" in decl:
        import out_family

        try:
            return out_family.render(decl, header)
        except out_family.FamilyError as e:
            raise GenError(str(e)) from None
    ptx = ROOT / decl["ptx"]
    program = parse_ptx.parse(ptx.read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    lines = [
        "-- SPDX-License-Identifier: Apache-2.0",
        *header(decl["ptx"]),
        "module",
        "",
        *[
            f"public import {m}"
            for m in [
                "Lemmas.Flow.OutCoreRules" if "decoded" in decl else "Lemmas.Flow.OutLit",
                "Tactics.KernelRfl",
                *decl.get("imports", []),
            ]
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
    ops = decoded_ops(ROOT / decl["decoded"]) if "decoded" in decl else None
    for run in decl["runs"]:
        r = Run(code, ids, run)
        r.ops = ops
        lines += r.render(decl["kernel"], decl["code"], decl["assumptions"])
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
