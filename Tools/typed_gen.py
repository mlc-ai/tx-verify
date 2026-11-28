# SPDX-License-Identifier: Apache-2.0
"""Typed windows: tag tables and one strict segment per run of local instructions.

The typed mode of `Tools/out_gen.py` (`"typed"` in a declaration). A *window* is a path of a
kernel through straight-line local code and guarded branches whose outcome is stated:

    {"typed": {"ptx": "Kernels/K/k.ptx", "namespace": "PTX.Kernels.K.Gen", "output": "...lean",
               "kernel": "PTX.Kernels.K.kernel", "code": "PTX.Kernels.K.Flow",
               "imports": ["Kernels.K.Flow.Code"],
               "windows": [{"name": "win1", "start": 1299, "end": 1838,
                            "branches": {"1302": false, "1466": false}}],
               "events": [{"match": "^shfl", "tag": "dat32"}]}}

The generator (1) runs a forward abstract interpretation of the whole kernel over the control
flow: the *tag* of a register at a pc (a bit pattern of a width, a nonzero one, a predicate, an
`.f32` datum, a 64-bit value of two data) is the meet of the tags the paths bring; a local
instruction's transfer mirrors the rules of `Lemmas/Flow/TypedOpsF.lean`, `TypedMoveF.lean`,
`TypedFloatF.lean`, `TypedWidenF.lean`, an event's results get the tag of their class (`events`:
the well-formedness a role states once for loaded, shuffled and `tcgen05.ld` payloads); (2) cuts
each window into runs (maximal stretches of unguarded local instructions) and branches; (3) writes
the tags at the cuts (`qt`, restricted to the registers live there) and, for each run, one
theorem `SegQ kernel A L g (QTF qt) a F b G` proved by the `decide`-checked Boolean
`checkF absF qt a b [] [] ops` (`Lemmas/Flow/SegQF.lean`: `segQF_run`), and for the window one
theorem composing the runs with `SegQF.bra`, the branch predicates being hypotheses.

Single pieces: an instruction `mul`, `add`, `sub` `.f32`, `add`, `mul` `.f32x2`, `neg.f32`,
`lg2.approx.ftz.f32` or `cvt.rn.bf16x2.f32` without a rounding modifier is cut out of its run as
one piece `segQ_single` (`Lemmas/Flow/TypedSingleG.lean`); its step is a hypothesis of the window
(`SingleStep` at each pc of `<name>_singles`), proved once by the kernel, and the window's
invariant becomes `QTF qt ∧ TauAll R`. `"family": 3` takes the runs of `absF3` (`ex2`, `setp`),
`4` adds `absMovImm` (`mov.b32 d, 0f..`), `5` adds `mad.wide`, `bfe`, `not` and
`mov.pred d, imm` (`TypedIntG.lean`);
`"results"` tags the result of the instruction at the listed pcs (the software `exp2` blocks).

Nothing here is trusted: the Boolean is checked by the kernel, so a tag the analysis got wrong
fails the build. The hypotheses of a window are exactly what the typed engine cannot know: the
outcome of each branch (a fact of the control machine), the kernel's reading of the floating
forms (`FloatPlain`), and the registers its callers keep (`G`).
"""

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flow_gen  # noqa: E402
import parse_ptx  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
WIDTH = 100


CTL = ("bra", "brx", "ret", "exit", "call")


class TypedError(Exception):
    pass


# ---- tags: ("bits", w) ("nz", w) ("pred",) ("dat32",) ("dat64",) -------------------------------


def sat(have, need):
    """`TagF.sat`: the tag `have` serves a use that needs `need`."""
    if have is None:
        return False
    k, n = have[0], need[0]
    if n in ("bits", "nz"):
        if k in ("bits", "nz") and n == "bits":
            return have[1] == need[1]
        return k == "nz" and n == "nz" and have[1] == need[1]
    if n == "pred":
        return k == "pred"
    if n == "dat32":
        return have == ("dat32",) or (k in ("bits", "nz") and have[1] == 32)
    if n == "dat64":
        return have == ("dat64",) or (k in ("bits", "nz") and have[1] == 64)
    return False


def meet(a, b):
    """The tag both `a` and `b` serve: the weaker one, or none."""
    if a == b:
        return a
    if a is None or b is None:
        return None
    if sat(a, b):
        return b
    if sat(b, a):
        return a
    return None


def lean_tag(t):
    if t[0] in ("bits", "nz"):
        return f".old (.{t[0]} {t[1]})"
    if t[0] == "pred":
        return ".old .pred"
    return f".{t[0]}"


# ---- operands -----------------------------------------------------------------------------------

INT_IMM = re.compile(r"^-?(\d+|0[xX][0-9a-fA-F]+)$")
F32_IMM = re.compile(r"^0[fF][0-9a-fA-F]{8}$")
VEC = re.compile(r"^\{(.*)\}$")
ITYPE = re.compile(r"^([bus])(\d+)$")


def vec(o):
    m = VEC.match(o)
    return [x.strip() for x in m.group(1).split(",")] if m else None


def itype(s):
    m = ITYPE.match(s)
    return (m.group(1), int(m.group(2))) if m else None


class Analysis:
    """Forward tag analysis over the flattened code."""

    def __init__(self, code, ids, events, results=()):
        self.code, self.ids = code, ids
        self.results = {
            r["from"] + r["step"] * i + r["offset"]: r["tag"]
            for r in results
            for i in range(r["count"])
        }
        self.events = [(re.compile(e["match"]), e["tag"]) for e in events]
        self.n = len(code)
        self.regs = set(ids)

    # operand classes ------------------------------------------------------------------------
    def tag(self, env, o):
        return env.get(o)

    def rb(self, env, o):
        """A constant or a register of bits (any width)."""
        return bool(INT_IMM.match(o)) or (
            o in self.regs and (env.get(o) or ("",))[0] in ("bits", "nz")
        )

    def rw(self, env, o, w):
        """A constant or a register of exactly `w` bits."""
        if INT_IMM.match(o):
            return True
        t = env.get(o)
        return o in self.regs and t is not None and t[0] in ("bits", "nz") and t[1] == w

    def rp(self, env, o):
        return env.get(o) == ("pred",)

    # transfer -------------------------------------------------------------------------------
    def local(self, env, ins):
        """The (register, tag) pairs the local rules give an unguarded instruction, or None."""
        op = ins["opcode"].split(".")
        ops = ins["operands"]
        head = op[0]
        d = ops[0] if ops else None
        e = env
        ty = itype(op[-1]) if len(op) > 1 else None
        if head == "setp" and len(op) == 3 and ty and len(ops) == 3:
            if self.rb(e, ops[1]) and self.rb(e, ops[2]):
                return [(d, ("pred",))]
        elif head in ("add", "sub", "min", "max", "shl", "shr") and len(op) == 2 and ty:
            if len(ops) == 3 and self.rb(e, ops[1]) and self.rb(e, ops[2]):
                return [(d, ("bits", ty[1]))]
        elif head == "mul" and len(op) == 3 and ty and op[1] in ("lo", "hi", "wide"):
            if len(ops) == 3 and self.rb(e, ops[1]) and self.rb(e, ops[2]):
                return [(d, ("bits", 2 * ty[1] if op[1] == "wide" else ty[1]))]
        elif head == "mad" and len(op) == 3 and ty and op[1] == "lo" and len(ops) == 4:
            if all(self.rb(e, x) for x in ops[1:]):
                return [(d, ("bits", ty[1]))]
        elif head == "mad" and len(op) == 3 and ty and op[1] == "wide" and len(ops) == 4:
            if self.rb(e, ops[1]) and self.rb(e, ops[2]) and self.rw(e, ops[3], 2 * ty[1]):
                return [(d, ("bits", 2 * ty[1]))]
        elif head == "bfe" and len(op) == 2 and ty and len(ops) == 4:
            if all(self.rb(e, x) for x in ops[1:]):
                return [(d, ("bits", ty[1]))]
        elif head == "not" and len(op) == 2 and ty and ty[1] != 1 and len(ops) == 2:
            if self.rb(e, ops[1]):
                return [(d, ("bits", ty[1]))]
        elif head == "neg" and len(op) == 2 and ty and len(ops) == 2 and self.rb(e, ops[1]):
            return [(d, ("bits", ty[1]))]
        elif head in ("and", "or", "xor") and len(op) == 2 and len(ops) == 3:
            if op[1] == "pred":
                if self.rp(e, ops[1]) and self.rp(e, ops[2]):
                    return [(d, ("pred",))]
            elif ty and ty[1] != 1 and self.rb(e, ops[1]) and self.rb(e, ops[2]):
                return [(d, ("bits", ty[1]))]
        elif head == "selp" and len(op) == 2 and len(ops) == 4:
            a, b, p = ops[1], ops[2], ops[3]
            if op[1] == "f32":
                if self.rp(e, p) and all(
                    bool(F32_IMM.match(x)) or sat(e.get(x), ("dat32",)) for x in (a, b)
                ):
                    return [(d, ("dat32",))]
            elif ty and self.rw(e, a, ty[1]) and self.rw(e, b, ty[1]) and self.rp(e, p):
                return [(d, ("bits", ty[1]))]
        elif head == "mov" and len(op) == 2 and len(ops) == 2:
            return self.mov(e, op[1], ops)
        elif head == "cvt" and len(ops) == 2:
            if op[1:] == ["f32", "bf16"]:
                if e.get(ops[1]) == ("bits", 16):
                    return [(d, ("dat32",))]
            elif len(op) == 3:
                dt, st = itype(op[1]), itype(op[2])
                if dt and st and self.rb(e, ops[1]):
                    return [(d, ("bits", dt[1]))]
        elif ins["opcode"] == "max.f32" and len(ops) in (3, 4):
            if all(sat(e.get(x), ("dat32",)) for x in ops[1:]):
                return [(d, ("dat32",))]
        elif ins["opcode"] == "fma.rn.f32x2" and len(ops) == 4:
            if all(sat(e.get(x), ("dat64",)) for x in ops[1:]):
                return [(d, ("dat64",))]
        return None

    def mov(self, e, t, ops):
        d, a = ops
        if t == "pred":
            return [(d, ("pred",))] if self.rp(e, a) or INT_IMM.match(a) else None
        lo_hi = vec(d)
        ty = itype(t)
        if lo_hi and len(lo_hi) == 2 and ty:
            w = ty[1]
            tg = e.get(a)
            if tg == ("bits", w) or tg == ("nz", w):
                return [(x, ("bits", w // 2)) for x in lo_hi]
            if tg == ("dat64",) and w == 64:
                return [(x, ("dat32",)) for x in lo_hi]
            return None
        pair = vec(a)
        if pair and len(pair) == 2 and ty:
            w = ty[1]
            if w % 2 == 0 and w <= 64 and all(e.get(x) == ("bits", w // 2) for x in pair):
                return [(d, ("bits", w))]
            if w == 64 and all(sat(e.get(x), ("dat32",)) for x in pair):
                return [(d, ("dat64",))]
            return None
        if ty and len(ops) == 2:
            if ty[1] == 32 and F32_IMM.match(a):
                return [(d, ("dat32",))]
            if self.rw(e, a, ty[1]):
                return [(d, ("bits", ty[1]))]
            if a.startswith("%") and a not in self.regs and ty[1] > 1:
                return [(d, ("bits", ty[1]))]  # a special register is read as its bits
        return None

    FLOAT_OPS = (
        "add",
        "sub",
        "mul",
        "fma",
        "div",
        "rcp",
        "ex2",
        "lg2",
        "neg",
        "sqrt",
        "rsqrt",
        "min",
        "max",
        "abs",
    )

    def float_result(self, ins):
        """The result of a floating instruction no rule of the typed engine takes is still a datum
        (the outcome of its own segment, which a caller proves): the tag of the entry of the next
        window."""
        op = ins["opcode"].split(".")
        if op[0] == "setp" and op[-1] == "f32" and len(ins["writes"]) == 1:
            return [(ins["writes"][0], ("pred",))]
        if ins["opcode"] == "cvt.rn.bf16x2.f32" and len(ins["writes"]) == 1:
            return [(ins["writes"][0], ("dat32",))]
        if op[0] in self.FLOAT_OPS and op[-1] in ("f32", "f32x2") and len(ins["writes"]) == 1:
            return [(ins["writes"][0], ("dat64",) if op[-1] == "f32x2" else ("dat32",))]
        return None

    def event(self, env, ins):
        """The tags of an event's results: the class's well-formedness."""
        out = []
        op = ins["opcode"]
        width = None
        for tok in reversed(op.split(".")):
            m = ITYPE.match(tok) or re.match(r"^(f)(\d+)$", tok)
            if m:
                width = int(m.group(2))
                break
        for w in ins["writes"]:
            tg = None
            for rx, name in self.events:
                if rx.search(op):
                    tg = {"dat32": ("dat32",), "dat64": ("dat64",), "pred": ("pred",)}.get(name)
                    if tg is None and name.startswith("bits"):
                        tg = ("bits", int(name[4:]))
                    break
            else:
                if w.startswith("%p"):
                    tg = ("pred",)
                elif w.startswith("#") and op.startswith("mbarrier"):
                    tg = ("pred",)
                elif op.startswith("shfl"):
                    src = [r for r in ins["reads"] if r in self.regs]
                    tg = env.get(src[0]) if src else None
                    if tg is None and width:
                        tg = ("bits", width)
                elif width:
                    tg = ("bits", width)
            out.append((w, tg))
        return out

    def step(self, env, ins):
        out = dict(env)
        opc = ins["opcode"]
        if ins["guard"] is not None or ins["event"] or opc.startswith("ld.param"):
            res = self.event(env, ins)
        elif opc.split(".")[0] == "bra":
            return out
        else:
            hk = half_kind(ins)
            if hk is not None:
                r = (
                    [(ins["writes"][0], ("dat32",))]
                    if hk == "widen"
                    else [(w, None) for w in ins["writes"]]
                )
            else:
                r = self.local(env, ins)
            if r is None:
                r = self.float_result(ins)
            res = r if r is not None else [(w, None) for w in ins["writes"]]
        if opc.startswith("selp.b32") and len(ins["operands"]) == 4:
            # a select of 32-bit data: the result is one of the two operands
            _, sa, sb, _ = ins["operands"]
            if all(INT_IMM.match(x) or sat(env.get(x), ("dat32",)) for x in (sa, sb)):
                res = [(ins["writes"][0], ("dat32",))]
        tag = self.results.get(ins["pc"])
        if tag is not None and len(ins["writes"]) == 1:
            res = [(ins["writes"][0], ("bits", int(tag[4:])) if tag.startswith("bits") else (tag,))]
        for x in vec_names(ins["writes"]):
            out.pop(x, None)
        for w, tg in res:
            if tg is None:
                out.pop(w, None)
            else:
                out[w] = tg
        if ins["guard"] is not None:
            # a guarded instruction may be skipped: keep only what both outcomes agree on
            for w, tg in res:
                if env.get(w) != out.get(w):
                    m = meet(env.get(w), out.get(w))
                    if m is None:
                        out.pop(w, None)
                    else:
                        out[w] = m
        return out

    def run(self):
        n = self.n
        env_in = [None] * n
        env_in[0] = {}
        changed = True
        passes = 0
        while changed:
            changed = False
            passes += 1
            if passes > 60:
                raise TypedError("the tag analysis does not converge")
            for pc in range(n):
                cur = env_in[pc]
                if cur is None:
                    continue
                out = self.step(cur, self.code[pc])
                for q in flow_gen.all_successors(self.code[pc], n):
                    old = env_in[q]
                    if old is None:
                        env_in[q] = dict(out)
                        changed = True
                        continue
                    new = {}
                    for r, t in old.items():
                        # at a join the weakest tag the predecessors have in common
                        # (`tagsSatF` of `Lemmas/Flow/SegQFSat.lean` checks a jump)
                        m = meet(t, out.get(r))
                        if m is not None:
                            new[r] = m
                    if new != old:
                        env_in[q] = new
                        changed = True
        return env_in


def vec_names(names):
    return names


# ---- windows ------------------------------------------------------------------------------------


def local_unguarded(ins):
    return (
        ins["guard"] is None
        and not ins["event"]
        and ins["table"] is None
        and ins["opcode"].split(".")[0] not in ("bra", "brx", "ret")
    )


SINGLE = [
    (re.compile(r"^(add|sub|mul)(\.ftz)?\.f32$"), "dat32", 3),
    (re.compile(r"^(add|mul)\.f32x2$"), "dat64", 3),
    (re.compile(r"^neg\.f32$"), "dat32", 2),
    (re.compile(r"^lg2\.approx\.ftz\.f32$"), "dat32", 2),
    (re.compile(r"^cvt\.rn\.bf16x2\.f32$"), None, 3),
]


def single_need(ins):
    """The tag the register operands of a single piece must have (`None`: no need), or False when
    the instruction is no single piece (`TypedSingleG.singleNeeds`)."""
    if not local_unguarded(ins) or len(ins["writes"]) != 1:
        return False
    for rx, need, n in SINGLE:
        if rx.match(ins["opcode"]) and len(ins["operands"]) == n:
            return need or "none"
    return False


FLOAT_RUN = re.compile(
    r"^(ex2\.approx(\.ftz)?\.f32|setp\.[a-z]+(\.ftz)?\.f32|min\.f32|max\.f32|fma\.rn\.f32x?2?)$"
)


def run_supported(an, env, ins):
    """The instruction is one the typed runs take: a rule of `local`, a float rule of the families
    3 and 4, a constant move, or a single piece."""
    if not local_unguarded(ins):
        return False
    if single_need(ins) is not False or FLOAT_RUN.match(ins["opcode"]):
        return True
    if half_kind(ins) is not None:
        return True
    if ins["opcode"].startswith("mov.b32") and F32_IMM.match(ins["operands"][-1]):
        return True
    return an.local(env, ins) is not None


def auto_parts(windows, max_pcs, starts=None):
    """The windows grouped, in order, into parts of at most `max_pcs` instructions; with `starts`
    (the first pc of every part but the first) the parts begin exactly there."""
    parts, cur, n = [], [], 0
    for w in windows:
        size = w["end"] - w["start"]
        if starts is not None:
            if cur and w["start"] in starts:
                parts.append(cur)
                cur = []
        elif cur and n + size > max_pcs:
            parts.append(cur)
            cur, n = [], 0
        cur.append(w)
        n += size
    return parts + ([cur] if cur else [])


def single_tag(ins):
    """The tag a single piece writes (`TypedSingleG.singleNeeds`)."""
    return ("dat64",) if ins["opcode"].endswith("f32x2") else ("dat32",)


HALF = {"on": False}


def half_kind(ins):
    """`pack`, `unpack` or `widen` for an unguarded instruction of the bias path
    (`TypedHalfG.halfOuts`), else None; needs the declaration's `"half": true`."""
    if not HALF["on"] or not local_unguarded(ins):
        return None
    ops = ins["operands"]
    if ins["opcode"] == "cvt.f32.bf16" and len(ops) == 2:
        return "widen"
    if ins["opcode"] == "mov.b32" and len(ops) == 2:
        if vec(ops[1]) and not vec(ops[0]) and len(vec(ops[1])) == 2:
            return "pack"
        if vec(ops[0]) and len(vec(ops[0])) == 2 and not vec(ops[1]):
            return "unpack"
    return None


def half_outs(code, ids, pc):
    """The registers the bias piece at `pc` writes: (tagged ids, untagged ids)."""
    ins = code[pc]
    if half_kind(ins) == "widen":
        return [(ids[ins["writes"][0]], ("dat32",))], []
    return [], [ids[w] for w in ins["writes"]]


def split_block(code, a, b, auto):
    """The block `[a, b)` as windows of at most `max_pieces` pieces (runs and singles)."""
    pieces = cut_window(code, {"start": a, "end": b, "name": "x"}, auto.get("chunk", 100))
    step = auto.get("max_pieces", 8)
    out = []
    for i in range(0, len(pieces), step):
        grp = pieces[i : i + step]
        start, end = grp[0][1], grp[-1][2]
        out.append({"name": f"{auto['prefix']}{start}", "start": start, "end": end})
    return out


def auto_windows(an, env_in, code, auto):
    """One window per maximal block of supported instructions of `[from, to)` outside `skip`."""
    skip = {pc for a, b in auto.get("skip", []) for pc in range(a, b)}
    skip |= set(auto.get("skip_pcs", []))
    out, pc, end = [], auto["from"], auto["to"]
    while pc < end:
        a = pc
        while (
            pc < end
            and pc not in skip
            and env_in[pc] is not None
            and run_supported(an, env_in[pc], code[pc])
        ):
            pc += 1
        if pc > a:
            out += split_block(code, a, pc, auto)
        pc = max(pc, a) + (pc == a)
    out = cut_at(out, auto)
    if "part" in auto:
        index, max_pcs = auto["part"]
        parts = auto_parts(out, max_pcs, auto.get("part_starts"))
        return parts[index] if index < len(parts) else []
    return out


def cut_at(wins, auto):
    """The windows split at the `cut_pcs`: a jump target in the middle of a window needs a table."""
    cuts = sorted(set(auto.get("cut_pcs", [])))
    out = []
    for w in wins:
        pts = [w["start"]] + [c for c in cuts if w["start"] < c < w["end"]] + [w["end"]]
        for a, b in zip(pts, pts[1:]):
            out.append({"name": f"{auto['prefix']}{a}", "start": a, "end": b})
    return out


def gap_pcs(an, env_in, code, auto):
    """The pcs of `[from, to)` outside every window and every `skip`: the events, the branches and
    the instructions no typed rule takes. With `part`, those between the part's first window and
    the next part's (the first part starts at `from`)."""
    if not auto.get("gaps"):
        return []
    whole = {k: v for k, v in auto.items() if k != "part"}
    wins = auto_windows(an, env_in, code, whole)
    covered = {pc for w in wins for pc in range(w["start"], w["end"])}
    skip = {pc for a, b in auto.get("skip", []) for pc in range(a, b)}
    gaps = [
        pc
        for pc in range(auto["from"], auto["to"])
        if pc not in covered and pc not in skip and env_in[pc] is not None
    ]
    if "part" in auto:
        index, max_pcs = auto["part"]
        parts = auto_parts(wins, max_pcs, auto.get("part_starts"))
        if index >= len(parts):
            return []
        lo = parts[index][0]["start"] if index > 0 else auto["from"]
        hi = parts[index + 1][0]["start"] if index + 1 < len(parts) else auto["to"]
        gaps = [pc for pc in gaps if lo <= pc < hi]
    return gaps


def cut_window(code, w, chunk=100):
    """The runs [a, b) and branches of a window: ('run', a, b) and ('bra', pc, pick)."""
    pc, end = w["start"], w["end"]
    branches = {int(k): v for k, v in w.get("branches", {}).items()}
    items = []
    while pc < end:
        ins = code[pc]
        if single_need(ins) is not False:
            items.append(("single", pc, pc + 1, ins["writes"][0], single_tag(ins)))
            pc += 1
        elif half_kind(ins) is not None:
            items.append(("half", pc, pc + 1))
            pc += 1
        elif local_unguarded(ins):
            a = pc
            while (
                pc < end
                and local_unguarded(code[pc])
                and single_need(code[pc]) is False
                and half_kind(code[pc]) is None
            ):
                pc += 1
            n = -(-(pc - a) // chunk)  # pieces of about `chunk` instructions
            size = -(-(pc - a) // n)
            items += [("run", x, min(x + size, pc)) for x in range(a, pc, size)]
        elif pc in branches and ins["opcode"] == "bra" and ins["guard"] is not None:
            g = ins["guard"]
            if g["negated"]:
                raise TypedError(f"pc {pc}: a negated guard is not supported")
            items.append(("bra", pc, branches[pc], ins["target"], g["register"]))
            pc = ins["target"] if branches[pc] else pc + 1
        else:
            raise TypedError(f"pc {pc}: {ins['opcode']} is not a local instruction or a branch")
    if pc != end:
        raise TypedError(f"the window {w['name']} overshoots its end {end}")
    return items


def lean_list(items, indent):
    """A bracketed list, broken after commas at the line width."""
    lines, cur = [], "["
    pad = " " * indent
    for i, it in enumerate(items):
        piece = it + ("," if i + 1 < len(items) else "]")
        if len(cur) + len(piece) + 1 > WIDTH - 2 and cur.strip():
            lines.append(cur.rstrip())
            cur = pad
        cur += piece + " "
    if not items:
        cur = "[]"
    lines.append(cur.rstrip())
    return lines


def take_chain(codens, a, b):
    """The term `takeCode code_a <| takeCode code_(a+1) <| ... <| takeNil _ _` of a run, broken
    at the line width: the instruction list is read off the per-pc code lemmas."""
    lines, cur = [], "("
    for pc in range(a, b):
        piece = f"takeCode {codens}.code_{pc} <|"
        if cur and len(cur) + len(piece) + 7 > WIDTH:
            lines.append(cur)
            cur = ""
        cur = (cur + " " + piece) if cur != "(" else "(" + piece
    lines.append(cur + " takeNil _ _)")
    return lines


def lean_join(names):
    """`a ++ b ++ c` broken at the line width."""
    lines, cur = [], ""
    for i, n in enumerate(names):
        piece = n + (" ++" if i + 1 < len(names) else "")
        if cur and len(cur) + len(piece) + 1 > WIDTH - 4:
            lines.append(cur)
            cur = piece
        else:
            cur = (cur + " " + piece).strip()
    return lines + [cur]


def render_typed(decl, header):
    t = decl["typed"]
    HALF["on"] = bool(t.get("half"))
    program = parse_ptx.parse((ROOT / t["ptx"]).read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    ids = flow_gen.register_ids(function)
    an = Analysis(code, ids, t.get("events", []), t.get("results", []))
    env_in = an.run()
    live = flow_gen.liveness(code)
    kernel, ns = t["kernel"], t["namespace"]
    family = t.get("family", 1)
    windows = list(t.get("windows", []))
    if "auto" in t:
        windows += auto_windows(an, env_in, code, t["auto"])
    fam3 = family >= 3
    uses_single = any(
        single_need(code[pc]) is not False for w in windows for pc in range(w["start"], w["end"])
    )
    imports = ["Lemmas.Flow.SegQF", "Lemmas.Flow.SegQFCode"]
    if t.get("delta"):
        imports += ["Lemmas.Flow.SegQFD", "Lemmas.Flow.SegQFS"]
    if fam3 or uses_single:
        imports += ["Lemmas.Flow.SegQFJ", "Lemmas.Flow.TypedSingleG"]
    if family >= 4:
        imports.append("Lemmas.Flow.TypedMovImmG")
    if family == 5:
        imports.append("Lemmas.Flow.TypedIntG")
    if t.get("half"):
        imports.append("Lemmas.Flow.TypedHalfG")
    out = [
        "-- SPDX-License-Identifier: Apache-2.0",
        *header(t["ptx"]),
        "module",
        "",
        *[f"public import {m}" for m in imports + t.get("imports", [])],
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "open PTX PTX.Proof PTX.Flow PTX.Flow.TyG",
        "",
    ]
    st = None
    if t.get("delta"):
        preds = {pc: set() for pc in range(len(code))}
        for ins in code:
            for q in flow_gen.all_successors(ins, len(code)):
                preds[q].add(ins["pc"])
        st = {"keys": {}, "prev": None, "prev_pc": None, "preds": preds}
    gaps = gap_pcs(an, env_in, code, t["auto"]) if "auto" in t else []
    flow = (code, ids, env_in, live, st)
    for w in sorted(windows, key=lambda x: x["start"]):
        while gaps and gaps[0] < w["start"]:
            out += render_gap(gaps.pop(0), t["auto"]["prefix"], flow)
        out += render_window(
            w,
            (code, ids, env_in, live, st),
            (
                kernel,
                t["code"],
                t.get("chunk", 100),
                t["code_length"],
                family,
                ctl_set(t["ctl"]) if "ctl" in t else set(),
            ),
        )
    for pc in gaps:
        out += render_gap(pc, t["auto"]["prefix"], flow)
    out.append(f"end {ns}")
    return "\n".join(out) + "\n"


def render_gap(pc, prefix, flow):
    """The tags at a gap pc, as a cut of the chain of tables: the previous table with the
    registers written since in front, or the previous table itself when it is at this pc."""
    code, ids, env_in, live, st = flow
    env = dict(tag_env(env_in[pc], live[pc], ids))
    full = {ids[x]: t for x, t in env_in[pc].items() if x in ids}
    name = f"{prefix}g{pc}"
    out = [f"/-- The tags at the gap pc {pc}. -/"]
    shadow = None
    if st is not None and st["prev"] is not None:
        pp = st["prev_pc"]
        if pp == pc:
            out += [f"def {name} : EnvF := {st['prev']}"]
            shadow = {}
        else:
            written = {ids[x] for q in range(pp, pc) for x in code[q]["writes"] if x in ids}
            straight = all(code[q]["opcode"].split(".")[0] not in CTL for q in range(pp, pc))
            keys = st["keys"]
            if straight and pc - pp <= 60 and st["preds"][pc] <= {pc - 1}:
                if all(r in full for r in written if r in keys):
                    shadow = {r: full[r] for r in written if r in keys}
                    shadow |= {r: t for r, t in env.items() if r not in keys}
            if shadow is not None:
                body = lean_list([f"({r}, {lean_tag(t)})" for r, t in sorted(shadow.items())], 4)
                out += [f"def {name}_d : EnvF :="] + ["  " + ln for ln in body] + [""]
                out += [f"def {name} : EnvF := {name}_d ++ {st['prev']}"]
                st["keys"] = st["keys"] | shadow
    if shadow is None:
        body = lean_list([f"({r}, {lean_tag(t)})" for r, t in sorted(env.items())], 4)
        out += [f"def {name} : EnvF :="] + ["  " + ln for ln in body]
        if st is not None:
            st["keys"] = dict(env)
    if st is not None:
        st["prev"], st["prev_pc"] = name, pc
    out += [
        "",
        f"/-- The tags by pc of the gap pc {pc}. -/",
        f"def {name}_qt (pc : Nat) : EnvF := if pc = {pc} then {name} else []",
        "",
    ]
    return out


def tag_env(env, live_set, ids):
    """The tags at a pc of the live registers, in register-id order."""
    return sorted((ids[r], t) for r, t in env.items() if r in live_set and r in ids)


def window_cuts(items, w):
    """The pcs at which a window's tags are stated: its ends, the ends of runs and branches."""
    cuts = {w["start"], w["end"]}
    for it in items:
        if it[0] in ("run", "single", "half"):
            cuts |= {it[1], it[2]}
        else:
            cuts |= {it[1], it[3] if it[2] else it[1] + 1}
    return sorted(cuts)


def window_need(code, items, w, live):
    """The registers whose tags each cut states: those the rest of the window reads, and the
    exit set (`"exit": n` reads the next n instructions; default: the live registers)."""
    end = w["end"]
    span = w.get("exit")
    need = {end: set(live[end]) if span is None else set()}
    if span is not None:
        for pc in range(end, min(end + span, len(code))):
            need[end] |= set(code[pc]["reads"])
    for it in reversed(items):
        if it[0] == "bra":
            _, pc, pick, target, pred = it
            need[pc] = need[target if pick else pc + 1] | {pred}
            continue
        a, b = it[1], it[2]
        ue, wr = set(), set()
        for pc in range(a, b):
            ue |= set(code[pc]["reads"]) - wr
            wr |= set(code[pc]["writes"])
        need[a] = ue | (need[b] - wr)
    return need


def run_writes(code, ids, a, b):
    """The registers a run writes in the order of `wrF` (one entry per write)."""
    return [ids[r] for pc in range(a, b) for r in code[pc]["writes"] if r in ids]


def check_single(code, ids, env, pc, need):
    """The register operands of a single piece hold the datum its rule reads."""
    if need == "none":
        return
    for r in code[pc]["reads"]:
        if r in ids and not sat(env.get(r), (need,)):
            raise TypedError(f"pc {pc}: the operand {r} of {code[pc]['opcode']} is no {need}")


def ctl_set(spec):
    """The register ids of the control-live list `spec` (`"ctl": {"ids": [...], "ranges": [...]}`)."""
    ids = set(spec.get("ids", []))
    for lo, hi in spec.get("ranges", []):
        ids |= set(range(lo, hi + 1))
    return ids


def exact_flips(code, ids, live, a, b, ctl):
    """The pcs inside the straight stretch `[a, b)` where the exact and the typed pieces of the
    control machine's slicing (`sliceQ`) meet: a backward walk from the control registers live at
    `b`, an instruction is exact when it writes a register still needed."""
    need = {ids[r] for r in live[b] if r in ids and ids[r] in ctl}
    use = []
    for pc in range(b - 1, a - 1, -1):
        wr = {ids[r] for r in code[pc]["writes"] if r in ids}
        u = bool(wr & need)
        use.append(u)
        if u:
            need -= wr
            need |= {ids[r] for r in code[pc]["reads"] if r in ids}
    use.reverse()
    return [a + i for i in range(1, b - a) if use[i] != use[i - 1]]


def window_extras(code, ids, live, items, need, ctl):
    """The tables at the exact-piece boundaries inside the runs of a window: pc -> registers."""
    extras, i = {}, 0
    while i < len(items):
        if items[i][0] != "run":
            i += 1
            continue
        j = i
        while j + 1 < len(items) and items[j + 1][0] == "run":
            j += 1
        a, b = items[i][1], items[j][2]
        have = {it[1] for it in items} | {it[2] for it in items if it[0] != "bra"}
        for c in exact_flips(code, ids, live, a, b, ctl):
            if c in have:
                continue
            reads = set().union(*(set(code[pc]["reads"]) for pc in range(c, b)))
            wr = set().union(*(set(code[pc]["writes"]) for pc in range(c, b)))
            extras[c] = reads | (need[b] - wr)
        i = j + 1
    return extras


def render_window(w, flow, cfg):
    code, ids, env_in, live, st = flow
    kernel, codens, chunk, lenthm, family, ctl = cfg
    name = w["name"]
    items = cut_window(code, w, chunk)
    cuts = window_cuts(items, w)
    need = window_need(code, items, w, live)
    extras = window_extras(code, ids, live, items, need, ctl) if ctl else {}
    out = [f"/-! ## Window `{name}`: pcs {w['start']} to {w['end']} -/", ""]
    kinds = {}
    single_ends = {it[2]: it for it in items if it[0] == "single"}
    half_ends = {it[2]: it for it in items if it[0] == "half"}
    for c in cuts:
        if env_in[c] is None:
            raise TypedError(f"pc {c} is unreachable")
        env = dict(tag_env(env_in[c], need[c], ids))
        full = {ids[x]: t for x, t in env_in[c].items() if x in ids}
        shadow = None
        if st is not None and st["prev"] is not None and all(it[0] != "bra" for it in items):
            pp = st["prev_pc"]
            written = {ids[x] for pc in range(pp, c) for x in code[pc]["writes"] if x in ids}
            straight = all(code[pc]["opcode"].split(".")[0] not in CTL for pc in range(pp, c))
            keys = st["keys"]
            if straight and c - pp <= 60 and st["preds"][c] <= {c - 1}:
                if c in single_ends:
                    sd = ids[single_ends[c][3]]
                    if all(r in keys or r == sd for r in env):
                        shadow = {sd: single_tag(code[c - 1])}
                elif c in half_ends:
                    tg, wr = half_outs(code, ids, c - 1)
                    if all(r in keys or r in dict(tg) for r in env) and not any(
                        r in keys for r in wr
                    ):
                        shadow = dict(tg)
                elif all(r in full for r in written if r in keys):
                    shadow = {r: full[r] for r in written if r in keys}
                    shadow |= {r: t for r, t in env.items() if r not in keys}
        out += [f"/-- The tags at pc {c}. -/"]
        if shadow is not None:
            body = lean_list([f"({r}, {lean_tag(t)})" for r, t in sorted(shadow.items())], 4)
            out += [f"def {name}_d{c} : EnvF :="] + ["  " + ln for ln in body] + [""]
            out += [f"def {name}_t{c} : EnvF := {name}_d{c} ++ {st['prev']}", ""]
            st["keys"] = st["keys"] | shadow
            kinds[c] = True
        else:
            body = lean_list([f"({r}, {lean_tag(t)})" for r, t in sorted(env.items())], 4)
            out += [f"def {name}_t{c} : EnvF :="] + ["  " + ln for ln in body] + [""]
            if st is not None:
                st["keys"] = dict(env)
        if st is not None:
            st["prev"], st["prev_pc"] = f"{name}_t{c}", c
    for c, regs in sorted(extras.items()):
        if env_in[c] is None:
            raise TypedError(f"pc {c} is unreachable")
        env = tag_env(env_in[c], regs, ids)
        body = lean_list([f"({r}, {lean_tag(t)})" for r, t in env], 4)
        out += [f"/-- The tags at the exact-piece boundary {c}. -/", f"def {name}_x{c} : EnvF :="]
        out += ["  " + ln for ln in body] + [""]
    out += [f"/-- The tags of the window `{name}` at its cuts. -/", f"def {name}_qt : Nat → EnvF"]
    out += [f"  | {c} => {name}_t{c}" for c in cuts]
    out += [f"  | {c} => {name}_x{c}" for c in sorted(extras)] + ["  | _ => []", ""]
    qt = f"{name}_qt"
    fam = str(family) if family >= 3 else ""
    parts = [it for it in items if it[0] in ("run", "single", "half")]
    halves = [it[1] for it in parts if it[0] == "half"]
    if halves:
        out += [
            f"/-- The pcs of the bias pieces of the window `{name}`. -/",
            f"def {name}_halves : List Nat := {halves}",
            "",
            f"/-- The registers the bias pieces of `{name}` write: tagged, untagged. -/",
            f"def {name}_ho (pc : Nat) : EnvF × List Nat :=",
            "  (List.lookup pc [",
        ]
        for i, h in enumerate(halves):
            tg, wr = half_outs(code, ids, h)
            tl = ", ".join(f"({r}, {lean_tag(t)})" for r, t in tg)
            out.append(
                f"    ({h}, ([{tl}], {wr}))" + ("," if i + 1 < len(halves) else "]).getD ([], [])")
            )
        out.append("")
    for it in parts:
        a = it[1]
        if it[0] == "half":
            out += [
                f"/-- The registers the bias piece at {a} writes. -/",
                f"abbrev {name}_wr_{a} : List Nat :=",
                f"  ({name}_ho {a}).1.map Prod.fst ++ ({name}_ho {a}).2",
                "",
            ]
            continue
        if it[0] == "single":
            check_single(code, ids, env_in[a], a, single_need(code[a]))
            out += [
                f"/-- The register the single piece at {a} writes. -/",
                f"def {name}_wr_{a} : List Nat := [{ids[it[3]]}]",
                "",
            ]
            continue
        b = it[2]
        wrs = run_writes(code, ids, a, b)
        out += [
            f"/-- The registers the run from {a} to {b} writes. -/",
            f"def {name}_wr_{a} : List Nat :=",
        ]
        out += ["  " + ln for ln in lean_list([str(r) for r in wrs], 4)]
        out += [
            "",
            f"/-- **The run from {a} to {b}** ({b - a} instructions) is a strict segment under the",
            "tags. -/",
            f"theorem {name}_run_{a} {{A : List Assumption}} {{L : Launch}} {{g : Nat}}",
            "    {F G : List (Nat × Value)}",
            f"    (hP : FloatPlain{fam and 3} A L g {a} {b}) (hW : ∀ p ∈ G, p.1 ∉ {name}_wr_{a})",
            "    (hG : ∀ p ∈ G, p ∈ F) :",
            f"    SegQ {kernel} A L g (QTF {qt}) {a} F {b} G :=",
        ]
        if kinds.get(b):
            out += [
                f"  segQFD_run {qt} (Δ := {name}_d{b}) (W := {name}_wr_{a}) (by decide)",
                f"    (by have := {lenthm}; omega) (absF{fam}_sound hP) rfl",
                "    (checkD_ops",
                *["      " + ln for ln in take_chain(codens, a, b)],
                "      (by decide +kernel)) hW hG",
                "",
            ]
            continue
        out += [
            f"  segQF{fam}_runW {qt} (by decide)",
            f"    (by have := {lenthm}; omega) hP (checkW_ops",
            *["      " + ln for ln in take_chain(codens, a, b)],
            "      (by decide +kernel)) hW hG",
            "",
        ]
    singles = [it[1] for it in parts if it[0] == "single"]
    if singles:
        out += [
            f"/-- The pcs of the single pieces of the window `{name}`. -/",
            f"def {name}_singles : List Nat := {singles}",
            "",
        ]
    if halves:
        out += [
            f"/-- The bias pieces of `{name}` are the instructions `halfOuts` reads. -/",
            f"theorem {name}_ho_ok : ∀ pc ∈ {name}_halves, ∀ op,",
            f"    {kernel}.code[pc]? = some ⟨none, op⟩ →",
            f"      halfOuts op = some ({name}_ho pc) := by",
            "  intro pc hm op hc",
            f"  simp only [{name}_halves, List.mem_cons, List.not_mem_nil, or_false] at hm",
            f"  rcases hm with {' | '.join(['rfl'] * len(halves))}",
        ]
        for h in halves:
            out.append(f"  · rw [{codens}.code_{h}] at hc; cases hc; decide +kernel")
        out.append("")
    out += [
        f"/-- The registers the window `{name}` writes. -/",
        f"def {name}_wr : List Nat :=",
        *["  " + ln for ln in lean_join([f"{name}_wr_{it[1]}" for it in parts])],
        "",
    ]
    for it in parts if singles or halves else []:
        a = it[1]
        wra = f"{name}_wr_{a}"
        out += [
            f"theorem {name}_sub_{a} : ∀ x ∈ {wra}, x ∈ {name}_wr := by",
            "  decide +kernel",
            "",
        ]
    out += render_compose(
        w,
        items,
        (ids, name, qt, kernel, codens),
        (fam, bool(singles or halves), kinds, bool(singles), bool(halves)),
    )
    return out


def mem_proof(k, n, h):
    """`h` as a member of the left-nested append of `n` lists, from the list number `k`."""
    term = h
    if k > 0:
        term = f"(memR {term})"
    for _ in range(n - 1 - k):
        term = f"(memL {term})"
    return term


def render_compose(w, items, names, mode):
    ids, name, qt, kernel, codens = names
    fam, tau, kinds, has_s, has_h = mode
    start, end = w["start"], w["end"]
    brs = [it for it in items if it[0] == "bra"]
    used = any(it[0] in ("run", "bra") for it in items)
    hyps = []
    if has_s:
        hyps.append(f"    (hS : ∀ pc ∈ {name}_singles,")
        hyps.append(f"      SingleStep {kernel} A L g R pc)")
    if has_h:
        hyps.append(f"    (hH : ∀ pc ∈ {name}_halves,")
        hyps.append(f"      HalfStepO {kernel} A L g R pc ({name}_ho pc))")
    for i, b in enumerate(brs):
        pick = "true" if b[2] else "false"
        hyps.append(f"    (hB{i + 1} : ∀ u, At u {b[1]} G → QTF {qt} u →")
        hyps.append(f"      u.regs {ids[b[4]]} = some (.pred {pick}))")
    q = f"(QTF {qt})"
    if tau:
        q = f"(fun t => QTF {qt} t ∧ TauAll {kernel} A L g R t)"
    sq = [f"    SegQ {kernel} A L g {q} {start} F {end} G := by"]
    if tau:
        sq = [
            f"    SegQ {kernel} A L g",
            f"      (fun t => QTF {qt} t ∧",
            f"        TauAll {kernel} A L g R t) {start} F {end} G := by",
        ]
    pl = ".plain.plain" if fam else ""
    out = [
        f"/-- **The window `{name}`** from pc {start} to pc {end}: its runs and branches, the",
        "predicate of each branch assumed to read the outcome the path takes. -/",
        f"theorem {name} {{A : List Assumption}} {{L : Launch}} {{g : Nat}}",
        "    {R : TState → Prop} {F G : List (Nat × Value)}"
        if tau
        else "    {F G : List (Nat × Value)}",
        f"    ({'hP' if used else '_hP'} : FloatPlain{fam and 3} A L g {start} {end})",
        f"    (hW : ∀ p ∈ G, p.1 ∉ {name}_wr)",
        "    (hG : ∀ p ∈ G, p ∈ F)",
        *hyps,
    ]
    out[-1] += " :"
    out += sq
    acc, bi, k = None, 0, 0
    parts = [it for it in items if it[0] in ("run", "single", "half")]
    idx = {it[1]: i for i, it in enumerate(parts)}

    def sub(a, h):
        return f"({name}_sub_{a} _ {h})" if tau else mem_proof(idx[a], len(parts), h)

    for it in items:
        if it[0] in ("run", "single", "half"):
            a = it[1]
            fin = "F" if acc is None else "G"
            hg = "hG" if acc is None else "(fun p hp => hp)"
            if it[0] == "half":
                delta = bool(kinds.get(a + 1))
                out += [
                    f"  have r{a} := segQ_half{'E' if delta else 'D'} (qt := {qt}) (R := R)",
                    f"    (F := {fin}) (G := G) {codens}.code_{a} (by decide +kernel)",
                    f"    {'rfl (by decide +kernel)' if delta else '(by decide +kernel)'}",
                    f"    (hH {a} (by decide +kernel)) {hg}",
                    f"    (fun p hp h => hW p hp ({name}_sub_{a} _ h))",
                ]
            elif it[0] == "single" and kinds.get(a + 1):
                tag = lean_tag(it[4])
                out += [
                    f"  have r{a} := segQ_singleD (qt := {qt}) (R := R) (F := {fin}) (G := G)",
                    f"    (d := {ids[it[3]]}) (tg := {tag}) {codens}.code_{a}",
                    f"    (by decide +kernel) (by decide +kernel) rfl (hS {a} (by decide +kernel))",
                    f"    {hg}",
                    f"    (fun p hp h => hW p hp ({name}_sub_{a} _ (by simp [{name}_wr_{a}, h])))",
                ]
            elif it[0] == "single":
                out += [
                    f"  have r{a} := segQ_single (qt := {qt}) (R := R) (F := {fin}) (G := G)",
                    f"    (d := {ids[it[3]]}) {codens}.code_{a} (by decide +kernel)",
                    f"    (hS {a} (by decide +kernel)) {hg}",
                    f"    (fun p hp h => hW p hp ({name}_sub_{a} _ (by simp [{name}_wr_{a}, h])))",
                ]
            else:
                out += [
                    f"  have r{a} := {name}_run_{a} (F := {fin}) (G := G)",
                    "    (hP.mono (by omega) (by omega))",
                    f"    (fun p hp h => hW p hp {sub(a, 'h')}) {hg}",
                ]
                if tau:
                    out.append(f"  have r{a} := SegQ.tauAll R r{a}")
            if acc is None:
                acc = f"r{a}"
            else:
                k += 1
                out.append(f"  have c{k} := SegQ.comp {acc} r{a}")
                acc = f"c{k}"
        else:
            _, pc, pick, _, _ = it
            if acc is None:
                raise TypedError(f"pc {pc}: a window cannot start with a branch")
            bi += 1
            bra = "SegQT.bra" if tau else "SegQF.bra"
            out += [
                f"  have s{pc} := {bra} {'true' if pick else 'false'} {acc} {codens}.code_{pc}",
                f"    (fun t x hx => hP{pl}.bra t x _ _ hx)",
                f"    (hP{pl}.segs {pc} (by omega) (by omega)) (by decide +kernel) hB{bi}",
            ]
            acc = f"s{pc}"
    out.append(f"  exact {acc}")
    return out


def part_windows(decl):
    """The windows (as dicts with name, start, end, singles) of one typed part declaration."""
    t = decl["typed"]
    HALF["on"] = bool(t.get("half"))
    program = parse_ptx.parse((ROOT / t["ptx"]).read_text())
    function = next(f for f in program.functions if not f.declaration)
    code = flow_gen.flatten(function)
    an = Analysis(code, flow_gen.register_ids(function), t.get("events", []), t.get("results", []))
    env_in = an.run()
    out = list(t.get("windows", []))
    if "auto" in t:
        out += auto_windows(an, env_in, code, t["auto"])
    gaps = gap_pcs(an, env_in, code, t["auto"]) if "auto" in t else []
    for pc in gaps:
        out.append({"name": f"{t['auto']['prefix']}g{pc}", "start": pc, "end": pc, "gap": True})
    for w in out:
        if w.get("gap"):
            continue
        items = cut_window(code, w, t.get("chunk", 100))
        w["singles"] = [it[1] for it in items if it[0] == "single"]
        w["halves"] = [it[1] for it in items if it[0] == "half"]
        w["tau"] = bool(w["singles"] or w["halves"])
    return out


def dispatch_tree(names, indent):
    """`names` is a list of (start, window table); a decision tree on the program counter."""
    pad = "  " * indent
    if len(names) == 1:
        return [f"{pad}{names[0][1]} pc"]
    mid = len(names) // 2
    return [
        f"{pad}if pc < {names[mid][0]} then",
        *dispatch_tree(names[:mid], indent + 1),
        f"{pad}else",
        *dispatch_tree(names[mid:], indent + 1),
    ]


def render_lane(decl, header):
    """The table by pc of a typed region (no `part`), or each window of one part as a segment
    under it (`part`: the index in `parts`)."""
    t = decl["typed_lane"]
    parts = []
    for path in t["parts"]:
        d = json.loads((ROOT / path).read_text())
        parts.append((d["typed"]["namespace"], d["typed"]["kernel"], part_windows(d)))
    wins = sorted(((w["start"], ns, w) for ns, _, ws in parts for w in ws), key=lambda x: x[0])
    starts = {s for s, _, _ in wins}
    kns, kernel = parts[0][1].rsplit(".", 1)
    ns = t["namespace"]
    qt = t["qt"]
    part = t.get("part")
    mine = parts if part is None else [parts[part]]
    out = [
        "-- SPDX-License-Identifier: Apache-2.0",
        *header(t["ptx"]),
        "module",
        "",
        *(
            ["public import Lemmas.Flow.SegQFQt"]
            if part is None
            else [f"public import {t['qt_module']}"]
        ),
        *[f"public import {m}" for m in (t["imports"] if part is None else [t["imports"][part]])],
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "open PTX PTX.Proof PTX.Flow PTX.Flow.TyG",
        f"open {kns}",
        *[f"open {pns}" for pns, _, _ in mine],
        "",
    ]
    if part is None:
        out += [
            "/-- **The tags by program counter** of the typed region: the table of the window that",
            "starts last at or before the pc (a window's table is empty away from its cuts). -/",
            f"def {qt} (pc : Nat) : EnvF :=",
            *dispatch_tree([(s, f"{w['name']}_qt") for s, wns, w in wins], 1),
            "",
            "/-- The invariant of a lane: the tags by pc, and a fact of the states the local steps",
            "reach. -/",
            "def LQ (A : List Assumption) (L : Launch) (g : Nat) (R : TState → Prop) (t : TState) :",
            "    Prop :=",
            f"  QTF {qt} t ∧ TauAll {kernel} A L g R t",
            "",
        ]
        wins = []
    else:
        wins = [x for x in wins if x[1] == parts[part][0]]
    for s, wns, w in wins:
        if w.get("gap"):
            continue
        nm, a, b = w["name"], w["start"], w["end"]
        ca = "(Or.inl rfl)"
        cb = "(Or.inr (by decide +kernel))" if b in starts else "(Or.inl rfl)"
        hs = (
            f"    (hS : ∀ pc ∈ {nm}_singles, SingleStep {kernel} A L g R pc)"
            if w["singles"]
            else f"    (_hS : ∀ pc ∈ ([] : List Nat), SingleStep {kernel} A L g R pc)"
        )
        hh = (
            f"    (hH : ∀ pc ∈ {nm}_halves,\n      HalfStepO {kernel} A L g R pc ({nm}_ho pc)) :"
            if w["halves"]
            else "    (_hH : ∀ pc ∈ ([] : List Nat),\n"
            f"      HalfStepO {kernel} A L g R pc ([], [])) :"
        )
        args = " ".join(
            ["hP hW hG"] + (["hS"] if w["singles"] else []) + (["hH"] if w["halves"] else [])
        )
        out += [
            f"/-- The window `{nm}` (pcs {a} to {b}) as a segment of the lane. -/",
            f"theorem lw_{nm} {{A : List Assumption}} {{L : Launch}} {{g : Nat}}",
            "    {R : TState → Prop} {F G : List (Nat × Value)}",
            f"    (hP : FloatPlain3 A L g {a} {b}) (hW : ∀ p ∈ G, p.1 ∉ {nm}_wr)",
            "    (hG : ∀ p ∈ G, p ∈ F)",
            hs,
            hh,
            f"    SegQ {kernel} A L g (LQ A L g R) {a} F {b} G :=",
        ]
        if w["tau"]:
            out += [f"  qtfT_conv ({nm} {args}) {ca} {cb}", ""]
        else:
            out += [f"  SegQ.tauAll R (qtf_conv ({nm} {args}) {ca} {cb})", ""]
    out.append(f"end {ns}")
    return "\n".join(out) + "\n"
