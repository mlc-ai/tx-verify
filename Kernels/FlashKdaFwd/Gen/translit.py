# SPDX-License-Identifier: Apache-2.0
"""Transliteration of the local instructions of one path into terms over the register file.

A state of the generated machine holds a register file: `d.w id` is the word of an integer
register, `d.p id` the Boolean of a predicate register, `d.x id` the value of a data register
(`analysis.data_registers`). `PathTerms` walks the local instructions of a path between two
sites and gives, for every register the path assigns, the term the code computes for it from the
file at the start of the path, in the vocabulary of `Lemmas/Flow/Arith32.lean` and
`Arith32Wide.lean` (through `Tools/machine_gen.py`) and of the kernel's own `Proof/Thread/Base.lean`
for the forms those do not have. The terms are what the Lean segment proofs close by `rfl`, so a
wrong term makes a proof fail; nothing here is trusted.

A library of `emit.py` and `thread.py`: it writes no file, so there is nothing to regenerate
or to check. Its one command is a reading aid: it reads the frozen PTX (through `analysis.load`)
and prints the transliteration of the straight code from instruction LO to instruction HI - 1.

    python3 Kernels/FlashKdaFwd/Gen/translit.py LO HI
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "Tools"))
import machine_gen  # noqa: E402
from machine_gen import GenError, imm, lean_int  # noqa: E402

SREG = {
    "%tid.x": "(sreg ((L.tidOf g).get .x))",
    "%ctaid.x": "(sreg ((L.ctaidOf (g / L.block)).get .x))",
    "%ctaid.y": "(sreg ((L.ctaidOf (g / L.block)).get .y))",
    "%cluster_ctaid.x": "(sreg ((L.clusterCtaidOf (g / L.block)).get .x))",
    "%cluster_ctaid.y": "(sreg ((L.clusterCtaidOf (g / L.block)).get .y))",
    "%cluster_ctaid.z": "(sreg ((L.clusterCtaidOf (g / L.block)).get .z))",
    "%cluster_ctarank": "(sreg (L.rankOfCta (g / L.block)))",
    "shared_mem": "(sreg L.sharedBase)",
}
FLOAT_IMM = re.compile(r"0[fF]([0-9a-fA-F]{8})")


class Unsupported(GenError):
    """An instruction form the transliteration has no term for yet."""


class PathTerms(machine_gen.Stretch):
    """The terms of the registers one path assigns, over the file `d` at its start."""

    def __init__(self, code, ids, data):
        super().__init__(code, ids, {})
        self.data = data
        self.values = {}  # data register -> Value term
        self.lets = []  # (name, type, term, comment)
        self.assigned = []  # registers in order of (last) assignment
        self.current = None  # the instruction being transliterated
        self.param_loads = False  # whether scalar parameter loads are transliterated
        # The special instructions at the start of a function (`special`), in order: what the
        # step's proof needs, and for a `mapa` the position of its binder among the lets.
        self.head = []

    def resolve(self, text):
        """The register an operand names: itself, or the register of an inline-assembly scope
        that the flattened code reads or guards with under a scope-qualified name."""
        if text in self.ids or self.current is None:
            return text
        ins = self.current
        names = [*ins["reads"], *ins["writes"]]
        if ins["guard"] is not None:
            names.append(ins["guard"]["register"])
        for name in names:
            if name.endswith("#" + text):
                return name
        return text

    # Operands ---------------------------------------------------------------------------

    def word(self, text):
        if imm(text):
            return f"(i32 {lean_int(text)})"
        if text in SREG:
            return SREG[text]
        text = self.resolve(text)
        if text in self.bits:
            return self.bits[text]
        if text in self.data:
            raise Unsupported(f"integer read of the data register {text}")
        if text not in self.ids:
            raise Unsupported(f"operand {text}")
        return f"(d.w {self.ids[text]})"

    def pred(self, text):
        text = self.resolve(text)
        if text in self.preds:
            return self.preds[text]
        if text not in self.ids:
            raise Unsupported(f"predicate operand {text}")
        return f"(d.p {self.ids[text]})"

    def value(self, text):
        if text in self.values:
            return self.values[text]
        return f"(d.x {self.ids[text]})"

    # Instructions -----------------------------------------------------------------------

    def term(self, ins):
        op = ins["opcode"].split(".")
        o = ins["operands"]
        base = op[0]
        if base == "mov" and op[1] == "pred":
            if o[1] in ("0", "-1", "1"):
                return "pred", "false" if o[1] == "0" else "true"
            return "pred", self.pred(o[1])
        if base == "or" and op[1] == "pred":
            return "pred", f"({self.pred(o[1])} || {self.pred(o[2])})"
        if base == "and" and op[1] == "b32" and not imm(o[2]):
            return "bits", f"(and32 {self.word(o[1])} {self.word(o[2])})"
        if base == "cvt" and op[1:] == ["u32", "u64"]:
            return "bits", f"(low32 {self.word(o[1])})"
        if base == "cvt" and op[1:] == ["u16", "u32"]:
            return "bits16", f"(low16 {self.word(o[1])})"
        if base == "cvta" and op[1:] == ["to", "global", "u64"]:
            return "bits64", f"(r64 {self.word(o[1])})"
        if base == "mov" and op[1] in machine_gen.WIDE and imm(o[1]):
            return "bits64", f"(i64 {lean_int(o[1])})"
        if base == "mul" and op[1] == "lo" and op[2] in machine_gen.WIDE and imm(o[2]):
            return "bits64", f"(mul64 {self.word(o[1])} (i64 {lean_int(o[2])}))"
        if op[-1] in machine_gen.SHORT and base in ("sub", "and", "mul", "shr", "setp"):
            # An immediate operand has a form of its own (Core truncates an immediate once, and
            # reads a shift amount at 32 bits): the walk of a segment decides a branch from a
            # hypothesis up to reducible unfolding only, so the term is Core's exactly.
            if imm(o[2]) and not imm(o[1]):
                x, n = self.word(o[1]), lean_int(o[2])
                if base == "setp":
                    return "pred", f"(scmpi16 {machine_gen.CMP[op[1]]} {x} {n})"
                f = {"sub": "subi16", "and": "andi16", "mul": "muli16", "shr": "shrui16"}[base]
                return "bits16", f"({f} {x} {n})"
            if base == "sub" and imm(o[1]) and not imm(o[2]):
                return "bits16", f"(isub16 {lean_int(o[1])} {self.word(o[2])})"
            a = f"(i16 {lean_int(o[1])})" if imm(o[1]) else self.word(o[1])
            b = f"(i16 {lean_int(o[2])})" if imm(o[2]) else self.word(o[2])
            if base == "setp":
                return "pred", f"(scmp16 {machine_gen.CMP[op[1]]} {a} {b})"
            f = {"sub": "sub16", "and": "and16", "mul": "mul16", "shr": "shru16"}[base]
            return "bits16", f"({f} {a} {b})"
        if base == "ld" and op[1] == "param":
            # A scalar parameter: its bits, truncated to the load's width. (A read of a by-value
            # object through a pointer register has no term yet.)
            m = re.fullmatch(r"\[PARAM(\d+)\]", o[1])
            if m is None:
                raise Unsupported(f"pc {ins['pc']}: {ins['opcode']} through a register")
            if not self.param_loads:
                # The step of a segment with a parameter load needs cuts around the load.
                raise Unsupported(f"pc {ins['pc']}: {ins['opcode']} in a segment")
            width = {"b32": ("bits", "r32"), "b64": ("bits64", "r64")}[op[2]]
            return width[0], f"({width[1]} (paramBits L {m.group(1)}))"
        try:
            return super().term(ins)
        except GenError as e:
            raise Unsupported(str(e)) from None

    def step(self, ins):
        """Record what one local instruction assigns."""
        if ins["target"] is not None:
            return
        self.current = ins
        m = re.fullmatch(r"PARAM(\d+)", ins["operands"][-1]) if ins["operands"] else None
        if ins["opcode"] == "mov.b64" and m:
            # The address of a by-value parameter object: the register's static kind says it.
            if self.ids[ins["writes"][0]] != 2251 + int(m.group(1)):
                raise Unsupported(f"pc {ins['pc']}: parameter address in an unexpected register")
            return
        if ins["opcode"] == "cvta.param.u64":
            # The generic address of a by-value parameter object: the register's static kind
            # says it (`gparamPtr`), and evaluation runs the instruction.
            return
        if len(ins["writes"]) != 1:
            raise Unsupported(f"pc {ins['pc']}: {ins['opcode']} writes {ins['writes']}")
        reg = ins["writes"][0]
        if reg in self.data:
            m = FLOAT_IMM.fullmatch(ins["operands"][-1])
            if ins["opcode"] == "mov.b32" and m and ins["guard"] is None:
                # A constant moved into an opaque register: the slot holds the constant's bits.
                self.values[reg] = f"(.bits 32 (BitVec.ofNat 64 {int(m.group(1), 16)}))"
                if reg in self.assigned:
                    self.assigned.remove(reg)
                self.assigned.append(reg)
                return
            raise Unsupported(f"pc {ins['pc']}: data instruction {ins['opcode']}")
        res = self.term(ins)
        kind, t = res[0], res[1]
        rid = self.ids[reg]
        if ins["guard"] is not None:
            g = self.pred(ins["guard"]["register"])
            if ins["guard"]["negated"]:
                g = f"(!{g})"
            if kind == "pred":
                t = f"(if {g} then {t} else {self.pred(reg)})"
            else:
                t = f"(sel {g} {t} {self.word(reg)})"
        name = f"{'p' if kind == 'pred' else 'r'}{rid}"
        k = len([1 for n, *_ in self.lets if n == name or n.startswith(name + "'")])
        name += "'" * k
        text = ins["opcode"] + " " + ", ".join(ins["operands"])
        self.lets.append(
            (name, "Bool" if kind == "pred" else "BitVec 64", t, f"{ins['pc']}: {text}")
        )
        (self.preds if kind == "pred" else self.bits)[reg] = name
        if reg in self.assigned:
            self.assigned.remove(reg)
        self.assigned.append(reg)

    def run(self, pcs):
        for pc in pcs:
            self.step(self.code[pc])
        return self

    def head_special(self, ins, kind):
        """A special instruction at the start of a function: its destination's term, and the
        record the step's proof is written from (`self.head`)."""
        self.current = ins
        o, pc = ins["operands"], ins["pc"]
        reg = ins["writes"][0]
        rid = self.ids[reg]
        comment = f"{pc}: {ins['opcode']} " + ", ".join(o)
        if kind == "mapa":
            xa, xr = self.word(o[1]), self.word(o[2])
            self.head.append(("mapa", pc, xa, xr, len(self.lets), comment))
            self.values[reg] = "(mapaVal L g peer)"
        else:
            width = {"b32": "r32", "b64": "r64"}[ins["opcode"].split(".")[2]]
            if kind == "param":
                i = int(re.fullmatch(r"\[PARAM(\d+)\]", o[1]).group(1))
                t = f"({width} (paramBits L {i}))"
                self.head.append(("param", pc, i))
            else:
                m = re.fullmatch(r"\[(%rd\d+)\+128\]", o[1])
                if m is None or width != "r32" or not 2251 <= self.ids[m.group(1)] <= 2261:
                    raise Unsupported(f"pc {pc}: {ins['opcode']} {o[1]}")
                i = self.ids[m.group(1)] - 2251
                t = f"(objField L {i})"
                self.head.append(("pobj", pc, i))
            name = f"r{rid}"
            self.lets.append((name, "BitVec 64", t, comment))
            self.bits[reg] = name
        if reg in self.assigned:
            self.assigned.remove(reg)
        self.assigned.append(reg)

    def updates(self, live):
        """The `setW` and `setP` lists of the path: the assigned registers that are live at its
        end (the others are dead and need no file entry)."""
        words = [(self.ids[r], self.bits[r]) for r in self.assigned if r in self.bits and r in live]
        preds = [
            (self.ids[r], self.preds[r]) for r in self.assigned if r in self.preds and r in live
        ]
        return words, preds


def _opaque(self, live):
    """The `valueEx` list of the path: the opaque registers it assigns that are live at its end."""
    return [(self.ids[r], self.values[r]) for r in self.assigned if r in self.values and r in live]


PathTerms.opaque = _opaque


def demo(lo, hi):
    """Print the transliteration of the straight code `lo ≤ pc < hi` (for inspection)."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import analysis

    code, ids, _ = analysis.load()
    data = analysis.data_registers(code)
    path = PathTerms(code, ids, data)
    for pc in range(lo, hi):
        ins = code[pc]
        if ins["event"]:
            print(f"    -- {pc}: event {ins['opcode']}")
            continue
        try:
            path.step(ins)
        except Unsupported as e:
            print(f"    -- {pc}: UNSUPPORTED {e}")
    for name, ty, t, comment in path.lets:
        print(f"    let {name} : {ty} := {t}  -- {comment}")


if __name__ == "__main__":
    demo(int(sys.argv[1]), int(sys.argv[2]))


def special(ins, terms):
    """Whether evaluation cannot run the local instruction `ins`: a scalar parameter load or a
    read of a parameter object's field (they need a launch fact), a `mapa` (the launch may give
    no peer), the first instruction of a data run (`"run"`: it continues under a condition on
    opaque values). The step's proof takes each as a piece of its own
    (`Proof/Thread/EventLib.lean`)."""
    op = ins["opcode"]
    if op.startswith("ld.param"):
        if re.fullmatch(r"\[PARAM(\d+)\]", ins["operands"][1]):
            return None if terms.param_loads else "param"
        return "pobj"
    if op.startswith("mapa."):
        return "mapa"
    if is_run_item(ins, terms.data):
        return "run"
    return None


def is_run_item(ins, data):
    """A local instruction that writes an opaque register: an item of a data run (the data
    path, and the arithmetic on generic shared pointers). The exception: a constant moved into
    an opaque register is control code (`PathTerms.step`: the slot holds the constant's bits)."""
    if ins["event"] or ins["target"] is not None or ins["guard"] is not None:
        return False
    if ins["opcode"].startswith("mapa."):
        return False
    if ins["opcode"] == "mov.b32" and FLOAT_IMM.fullmatch(ins["operands"][-1]):
        return False
    return any(w in data for w in ins["writes"])


def tree(code, ids, data, start, terms=None, depth=0, fresh=True):
    """The decision tree of the local code from `start` to the next cut points: a leaf
    `("site", pc, terms)` at an event instruction, a leaf `("tail", pc, terms)` at a special
    instruction that evaluated code precedes (the code from there is the function `tail_<pc>`),
    or `("if", pred term, taken, fallthrough, terms)` at a guarded branch, with the lets of each
    straight piece collected in its `terms`. Special instructions at the very start (`fresh`)
    are part of the function (`PathTerms.head_special`)."""
    terms = terms or PathTerms(code, ids, data)
    pc = start
    seen = set()
    while True:
        ins = code[pc]
        if ins["event"]:
            return ("site", pc, terms)
        if pc in seen:
            raise Unsupported(f"local loop at {pc}")
        seen.add(pc)
        kind = special(ins, terms)
        if kind == "run":
            # A data run is always a function of its own (`emit.RunTail`), also at the start.
            return ("tail", pc, terms)
        if kind is not None and ins["guard"] is None:
            if not fresh:
                return ("tail", pc, terms)
            terms.head_special(ins, kind)
            pc += 1
            continue
        fresh = False
        if ins["target"] is not None:
            if ins["guard"] is None:
                pc = ins["target"]
                continue
            terms.current = ins
            g = terms.pred(ins["guard"]["register"])
            import copy

            left, right = copy.copy(terms), copy.copy(terms)
            for t in (left, right):
                t.bits, t.preds, t.values = dict(terms.bits), dict(terms.preds), dict(terms.values)
                t.lets, t.assigned, t.head = [], list(terms.assigned), []
            taken = tree(code, ids, data, ins["target"], left, depth + 1, False)
            other = tree(code, ids, data, pc + 1, right, depth + 1, False)
            if ins["guard"]["negated"]:
                taken, other = other, taken
            return ("if", g, taken, other, terms)
        terms.step(ins)
        pc += 1
