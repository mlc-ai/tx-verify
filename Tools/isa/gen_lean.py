# SPDX-License-Identifier: Apache-2.0
"""Generate the instruction grammar layer `Core/Source/Isa/*.lean` from the vendored table.

    python3 Tools/isa/gen_lean.py           # write the Lean files
    python3 Tools/isa/gen_lean.py --check   # fail when a file differs from what would be written

The input is `Tools/isa/data/table.json` (see `load_table.py`) with `extra.py`, the family
assignment of `families.py` and the cubes and fact tables of `constraints.py`. `build_model`
computes everything the Lean files and the Python grammar of `crosscheck.py` share: token and
slot numbering, slot codes, alignment masks, cube masks, fact tables and operand groups.

Numbering. Tokens are the modifier tokens of every slot, the dot-separated segments of
composite tokens and of mnemonics, and the operand type tokens. A slot's code of a token is
`1 + index` of the token in the slot's union of choices over all entries; code 0 is the omitted
value. A mask is a `Nat` with bit `code` set for every allowed value.
"""

import argparse
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import constraints  # noqa: E402
import families  # noqa: E402
from load_table import load  # noqa: E402

OUT = ROOT / "Core" / "Source" / "Isa"
WIDTH = 100
KEY_BASE = 128
FACT_BASE = 128

LEAN_KEYWORDS = set(
    "at by do else end fun if in let local match then with where from have show open import "
    "export namespace section variable universe def theorem lemma example abbrev instance class "
    "structure inductive deriving private protected partial unsafe noncomputable opaque axiom "
    "mutual attribute calc return for unless mut break continue try catch finally nomatch nofun "
    "sorry macro syntax notation infix infixl infixr prefix postfix true false global scoped "
    "termination_by decreasing_by Type Prop Sort set_option extends this".split()
)


def ident(text):
    """A Lean identifier for a token, slot or entry name."""
    out = text.replace("::", "_").replace(":", "_").replace(".", "_").replace("-", "_")
    if not out.replace("_", "").isalnum():
        raise ValueError(f"cannot name {text!r}")
    if out[0].isdigit():
        out = "x" + out
    if out in LEAN_KEYWORDS:
        out += "_"
    return out


class Model:
    pass


def build_model(final=None):
    table = load()
    final = final if final is not None else families.entries(table)
    m = Model()
    m.source = table["source"]
    m.final = final
    m.entries = [e for e in final if e["family"] != "excluded" and not e.get("alias_of")]
    m.aliases = [e for e in final if e.get("alias_of")]
    m.excluded = [e for e in final if e["family"] == "excluded"]
    # tokens
    toks = set()
    composites = {}
    slot_union = {}
    for e in m.entries:
        for name, choices, _ in e["slots"]:
            u = slot_union.setdefault(name, [])
            for c in choices:
                if c not in u:
                    u.append(c)
                toks.add(c)
                if "." in c:
                    segs = tuple(c.split("."))
                    if len(segs) not in (2, 3):
                        raise ValueError(f"composite token {c}")
                    composites[segs] = c
                    toks.update(segs)
        toks.update(e["mnemonic"].split("."))
        for op in e["operands"]:
            for d in op["dtype"]:
                if d is not None:
                    toks.add(constraints.normal_dtype(d))
    for e in m.excluded:
        toks.add(e["mnemonic"].split(".")[0])
    m.tokens = sorted(toks)
    m.tok_id = {t: ident(t) for t in m.tokens}
    if len(set(m.tok_id.values())) != len(m.tokens):
        raise ValueError("token identifiers collide")
    m.composites = composites
    m.slots = sorted(slot_union)
    m.slot_id = {s: ident(s) for s in m.slots}
    m.slot_union = slot_union
    m.entry_id = {e["name"]: ident(e["name"]) for e in m.entries}
    if len(set(m.entry_id.values())) != len(m.entries):
        raise ValueError("entry identifiers collide")
    # single-segment tokens get lookup keys
    m.keyed = sorted((key(t), t) for t in m.tokens if "." not in t)
    # heads
    m.heads = {}
    for e in m.entries:
        segs = e["mnemonic"].split(".")
        m.heads.setdefault(segs[0], []).append(e["name"])
    m.excluded_heads = {}
    for e in m.excluded:
        h = e["mnemonic"].split(".")[0]
        if h in m.heads:
            raise ValueError(f"head {h} has excluded and decoded entries")
        m.excluded_heads[h] = e["reason"]
    m.spec = {e["name"]: entry_spec(m, e) for e in m.entries}
    mark_pred_checks(m)
    return m


def mark_pred_checks(m):
    """Set `pred_check` on the register operands whose predicate-ness tells two entries apart.

    The grammar asks the predicate-register oracle only for those operands. Two entries of one
    mnemonic that both accept a synthesized instruction of one of them when predicate-ness is
    ignored differ at some operand position in whether the operand is a `.pred` register (for
    example cp.async's `src-size` and `ignore-src`); both operands at that position are marked.
    The cross-check verifies that every synthesized instruction is then recognized by one entry.
    """
    import crosscheck

    for spec in m.spec.values():
        for _, members in spec["groups"]:
            for op in members:
                op["pred_check"] = False
    crosscheck.prepare(m)

    def flat(name):
        return [op for _, ms in m.spec[name]["groups"] for op in ms]

    for e in m.entries:
        others = [n for n in m.heads[e["mnemonic"].split(".")[0]] if n != e["name"]]
        if not others:
            continue
        for cube in constraints.cubes(e):
            rep = tuple(sorted(s)[0] for s in cube)
            ts = crosscheck.op_tokens(m, crosscheck.opcode_of(e, rep))
            ops = crosscheck.synth_operands(m, e, rep)
            for n in others:
                r = crosscheck.try_entry(m, m.by_name[n], ts[1:], ops)
                if r is None:
                    continue
                for a, b in zip(flat(e["name"]), flat(n), strict=False):
                    if {a["kind"], b["kind"]} <= {"reg", "regvar"} and (
                        a["dtype"] == ("const", "pred")
                    ) != (b["dtype"] == ("const", "pred")):
                        a["pred_check"] = b["pred_check"] = True


def key(seg):
    k = 0
    for ch in seg:
        n = ord(ch)
        if not 0 < n < KEY_BASE:
            raise ValueError(f"non-ASCII token {seg!r}")
        k = k * KEY_BASE + n
    return k


def code(m, slot, tok):
    return 0 if tok == "" else 1 + m.slot_union[slot].index(tok)


def entry_spec(m, e):
    slots = []
    for name, choices, optional in e["slots"]:
        mask = sum(1 << code(m, name, c) for c in choices)
        slots.append((name, optional, mask))
    cubes = []
    for cube in constraints.cubes(e):
        row = []
        for (name, _, _), vals in zip(e["slots"], cube, strict=True):
            row.append(sum(1 << code(m, name, v) for v in vals))
        cubes.append(row)
    ops = []
    for op in e["operands"]:
        spec = dict(op)
        for k in ("lanes", "dtype", "sink"):
            f = constraints.fact_table(e, op, k)
            if f[0] == "table":
                _, ks, rows = f
                coded = []
                for kv, v in rows:
                    acc = 0
                    for k_i, tok in zip(ks, kv, strict=True):
                        acc = acc * FACT_BASE + code(m, e["slots"][k_i][0], tok)
                    coded.append((acc, v))
                f = ("table", ks, coded)
            spec[k] = f
        if op["kind"] == "imm":
            if op["literal"] == "_":
                spec["imm"] = ("sink",)
            elif op["literal"] is not None:
                spec["imm"] = ("choices", [lit_value(op["literal"])])
            elif op["choices"] is not None:
                spec["imm"] = ("choices", [lit_value(c) for c in op["choices"]])
            else:
                spec["imm"] = ("free",)
        else:
            spec["imm"] = ("none",)
        ops.append(spec)
    groups = []
    i = 0
    while i < len(ops):
        o = ops[i]
        for kind, field in (("pipe", "pipe"), ("bracket", "bracket")):
            if o[field] is not None:
                j = i
                while j < len(ops) and ops[j][field] == o[field]:
                    j += 1
                members = ops[i:j]
                for mem in members:
                    if mem["lanes"] != ("const", 1) and not (mem["kind"] == "reg" and mem["group"]):
                        raise ValueError(f"{e['name']}: optional member in a {kind}")
                    if kind == "bracket" and mem["pipe"] is not None:
                        raise ValueError(f"{e['name']}: pipe inside a bracket")
                groups.append((kind, members))
                i = j
                break
        else:
            groups.append(("single", [o]))
            i += 1
    orders = []
    for perm in e.get("orders", []):
        inv = [perm.index(k) for k in range(len(perm))]
        orders.append((perm, inv))
    return {
        "prefix": e["mnemonic"].split(".")[1:],
        "slots": slots,
        "cubes": cubes,
        "groups": groups,
        "orders": orders,
    }


def lit_value(text):
    """Value of an integer literal (§4.5.1 spellings: hexadecimal, octal, binary, decimal)."""
    neg = text.startswith("-")
    t = text[1:] if neg else text
    if t.endswith("U"):
        t = t[:-1]
    if t[:2] in ("0x", "0X"):
        v = int(t[2:], 16) if len(t) > 2 else None
    elif t[:2] in ("0b", "0B"):
        v = int(t[2:], 2) if len(t) > 2 else None
    elif t.startswith("0") and len(t) > 1:
        v = int(t[1:], 8) if all(c in "01234567" for c in t[1:]) else None
    else:
        v = int(t) if t.isdigit() else None
    if v is None:
        return None
    return -v if neg else v


# --------------------------------------------------------------------------- Lean text


def header(m, title):
    return (
        "-- SPDX-License-Identifier: Apache-2.0\n\n"
        f"-- Generated by Tools/isa/gen_lean.py from Tools/isa/data/table.json (TIRx table.py at\n"
        f"-- {m.source['commit']}). Do not edit.\n"
        "module\n\n"
    )


def wrap_items(items, indent, first_prefix="", sep=", ", close=""):
    """Lay out `items` over lines of at most WIDTH characters."""
    lines = []
    cur = indent + first_prefix
    start = True
    for i, it in enumerate(items):
        piece = it + (sep.rstrip() if i < len(items) - 1 else close)
        cand = cur + ("" if start else " ") + piece
        if len(cand) > WIDTH and not start:
            lines.append(cur)
            cur = indent + "  " + piece
        else:
            cur = cand
        start = False
    lines.append(cur)
    return lines


def lean_list(items, indent, prefix="", close=""):
    if not items:
        return [indent + prefix + "[]" + close]
    one = indent + prefix + "[" + ", ".join(items) + "]" + close
    if len(one) <= WIDTH:
        return [one]
    return wrap_items(items, indent, prefix + "[", close="]" + close)


def nat(n):
    """A Nat literal, as an expression of shorter literals when it is long."""
    s = str(n)
    if len(s) <= 36:
        return s
    hi, lo = divmod(n, 10**36)
    return f"(Nat.add (Nat.mul {nat(hi)} (Nat.pow 10 36)) {lo})"


def contract(block_id, title, statement, source, extra=""):
    lines = [f"/-! ## {block_id} — {title}"]
    lines += wrap_text("Statement: " + statement, "  ")
    lines += ["", "Defs: *", "", "Source:"]
    for item in source if isinstance(source, list) else [source]:
        lines += wrap_text("- " + item.strip(), "    ")
    lines += ["", "Direction: representation"]
    if extra:
        lines += [""] + wrap_text("Effect: " + extra, "  ")
    lines.append("-/")
    return "\n".join(lines) + "\n"


def wrap_text(text, cont):
    lead = text[: len(text) - len(text.lstrip(" "))]
    words = text.lstrip(" ").split(" ")
    lines, cur = [], ""
    for w in words:
        cand = (cur + " " + w) if cur else lead + w
        if len(cand) > WIDTH and cur:
            lines.append(cur)
            cur = cont + w
        else:
            cur = cand
    lines.append(cur)
    return lines


def source_ref(m):
    return [
        f"the TIRx PTX table `{m.source['path']}` at commit {m.source['commit']} (sha256 "
        f"{m.source['sha256'][:16]}...), vendored as `Tools/isa/data/table.json`",
        "PTX ISA 9.5 §9.7 (instruction syntax, modifiers and operand lists)",
    ]


def gen_token(m):
    out = [header(m, "Token")]
    out.append("public import Core.Source.Syntax\n\n@[expose] public section\n\n")
    out.append(
        contract(
            "PROG-ISA-TOKEN",
            "modifier tokens and slots",
            "The grammar layer names every modifier token of the instruction table, every "
            "segment of a mnemonic and every operand type token by a constructor of `Token`, and "
            "every modifier position of an entry by a constructor of `Slot`. The file is "
            "generated from the vendored instruction table by `Tools/isa/gen_lean.py`.",
            source_ref(m),
            "A dot-free segment of an opcode is looked up by its key, the number whose base-128 "
            "digits are the segment's ASCII codes (`Token.ofKey?`, a balanced comparison tree). "
            "Tokens that contain dots are composites of two or three segments (`Token.comp2?`, "
            "`Token.comp3?`). `Slot.code s t` is the position of `t` in the union of the choices "
            "of slot `s` over all entries, counted from 1; 0 means that `t` is no choice of `s`.",
        )
    )
    out.append("\nnamespace PTX.Isa\n\n")
    out.append("/-- A modifier token, a mnemonic segment or an operand type token. -/\n")
    out.append("inductive Token where\n")
    for t in m.tokens:
        out.append(f"  | {m.tok_id[t]}\n")
    out.append("  deriving DecidableEq, Repr, Inhabited\n\n")
    # key tree
    out.append("/-- The token of a dot-free segment, given the segment's key. -/\n")
    out.extend(key_tree(m))
    out.append(
        "/-- The key of a segment from its UTF-8 bytes: ASCII codes as base-128 digits; `none`\n"
        "for any other byte. -/\n"
        "def segKey : List UInt8 → Nat → Option Nat\n"
        "  | [], k => some k\n"
        "  | b :: bs, k =>\n"
        "    let n := b.toNat\n"
        "    bif Nat.blt 0 n && Nat.blt n 128 then segKey bs (k * 128 + n) else none\n\n"
        "/-- The token spelled by a dot-free string. The string is read through its UTF-8 bytes, "
        "which\nthe kernel reduces much faster than `String.toList`. -/\n"
        "def Token.ofString? (s : String) : Option Token :=\n"
        "  (segKey s.toByteArray.data.toList 0).bind Token.ofKey?\n\n"
    )
    for n in (2, 3):
        args = " ".join("abc"[:n])
        out.append(f"/-- The composite token of {n} segments, if any. -/\n")
        out.append(f"def Token.comp{n}? ({args} : Token) : Option Token :=\n")
        items = [(s, c) for s, c in sorted(m.composites.items()) if len(s) == n]
        if not items:
            out.append("  none\n\n")
            continue
        out.append(f"  match {', '.join('abc'[:n])} with\n")
        for segs, c in items:
            pats = ", ".join("." + m.tok_id[s] for s in segs)
            out.append(f"  | {pats} => some .{m.tok_id[c]}\n")
        out.append(f"  | {', '.join(['_'] * n)} => none\n\n")
    out.append("/-- A modifier position of an instruction entry. -/\ninductive Slot where\n")
    for s in m.slots:
        out.append(f"  | {m.slot_id[s]}\n")
    out.append("  deriving DecidableEq, Repr, Inhabited\n\n")
    index = {t: i for i, t in enumerate(m.tokens)}
    for s in m.slots:
        fn = f"Slot.code_{m.slot_id[s]}"
        pairs = sorted((index[t], i) for i, t in enumerate(m.slot_union[s], 1))
        out.append(
            f"/-- Codes of slot `{s}`, by the token's constructor index. -/\n"
            f"def {fn} (i : Nat) : Nat :=\n"
        )
        out.extend(line + "\n" for line in wrap_text("  " + cmp_tree(pairs), "    "))
        out.append("\n")
    out.append("/-- The code of a token in a slot: its position among the slot's choices. -/\n")
    out.append("def Slot.code (s : Slot) (t : Token) : Nat :=\n  match s with\n")
    for s in m.slots:
        out.append(f"  | .{m.slot_id[s]} => Slot.code_{m.slot_id[s]} t.ctorIdx\n")
    out.append("\nend PTX.Isa\n")
    return "".join(out)


def cmp_tree(pairs):
    """A comparison tree on `i` mapping each key of `pairs` to its value, other keys to 0."""
    if len(pairs) == 1:
        k, v = pairs[0]
        return f"bif Nat.beq i {k} then {v} else 0"
    mid = len(pairs) // 2
    return (
        f"bif Nat.blt i {pairs[mid][0]} then ({cmp_tree(pairs[:mid])}) "
        f"else ({cmp_tree(pairs[mid:])})"
    )


def key_tree(m):
    """`Token.ofKey?` as a balanced tree of comparisons, split into definitions by depth."""
    out = []
    defs = []

    def node(lo, hi, depth, name):
        # returns expression lines for keys m.keyed[lo:hi]
        if hi - lo == 1:
            k, t = m.keyed[lo]
            return f"bif Nat.beq k {nat(k)} then some .{m.tok_id[t]} else none"
        mid = (lo + hi) // 2
        left = sub(lo, mid, depth + 1, name + "l")
        right = sub(mid, hi, depth + 1, name + "r")
        return f"bif Nat.blt k {nat(m.keyed[mid][0])} then {left} else {right}"

    def sub(lo, hi, depth, name):
        if hi - lo <= 2:
            return "(" + node(lo, hi, depth, name) + ")"
        fn = f"Token.ofKey_{name}"
        defs.append((fn, lo, hi, depth, name))
        return f"{fn} k"

    top = node(0, len(m.keyed), 0, "")
    emitted = []
    i = 0
    while i < len(defs):
        fn, lo, hi, depth, name = defs[i]
        body = node(lo, hi, depth, name)
        emitted.append((fn, body))
        i += 1
    for fn, body in reversed(emitted):
        out.append(f"def {fn} (k : Nat) : Option Token :=\n")
        out.extend(line + "\n" for line in wrap_text("  " + body, "    "))
        out.append("\n")
    out.append("def Token.ofKey? (k : Nat) : Option Token :=\n")
    out.extend(line + "\n" for line in wrap_text("  " + top, "    "))
    out.append("\n")
    return out


FAMILY_DOC = {
    "int": "integer, bit, logic and integer comparison or selection",
    "move": "register moves, packing and unpacking",
    "cvt": "conversions",
    "mem": "memory access, atomics and address conversion",
    "warp": "warp collectives",
    "ctl": "control flow",
    "float": "floating-point arithmetic and comparison",
    "barrier": "CTA and cluster barriers",
    "fence": "memory fences",
    "mbarrier": "mbarrier objects",
    "async": "asynchronous copies and tensor-map operations",
    "tc": "tcgen05 instructions",
    "clc": "cluster launch control",
    "matrix": "warp-level matrix instructions",
    "multimem": "multimem instructions",
    "texture": "texture and surface instructions",
    "misc": "other instructions",
    "unmodeled": "instructions without a family this round",
}


def fact_lean(m, f, kind):
    if f[0] == "const":
        return f"(.const {value_lean(m, f[1], kind)})"
    if f[0] == "slot":
        return f"(.slot {f[1]})"
    _, ks, rows = f
    rs = ", ".join(f"({k}, {value_lean(m, v, kind)})" for k, v in rows)
    return f"(.table [{', '.join(map(str, ks))}] [{rs}])"


def value_lean(m, v, kind):
    if kind == "lanes":
        return str(v)
    if kind == "sink":
        return "true" if v else "false"
    return "none" if v is None else f"(some .{m.tok_id[v]})"


def imm_lean(imm):
    if imm[0] == "choices":
        return "(.choices [" + ", ".join(f"({v} : Int)" for v in imm[1]) + "])"
    return "." + imm[0]


def opspec_lean(m, op, indent):
    """An `OpSpec` as an anonymous constructor, wrapped to the line width."""
    fields = [
        f'"{op["name"]}"',
        f".{op['kind']}",
        f".{op['rw']}",
        "true" if op["group"] else "false",
        "true" if op["pred_check"] else "false",
        imm_lean(op["imm"]),
        fact_lean(m, op["lanes"], "lanes"),
        fact_lean(m, op["dtype"], "dtype"),
        fact_lean(m, op["sink"], "sink"),
    ]
    return wrap_items(fields, indent, "⟨", close="⟩")


def lst(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def gen_entry(m):
    out = [header(m, "Entry")]
    out.append("public import Core.Source.Isa.Token\n\n@[expose] public section\n\n")
    quotes = []
    for e in m.entries:
        for q in ([e["syntax"]] if e.get("extra") else []) + e.get("quotes", []):
            sec = str(e.get("section") or "").lstrip("§")
            item = f'§{sec}: "{q}"' if sec else f'"{q}"'
            if item not in quotes:
                quotes.append(item)
    out.append(
        contract(
            "PROG-ISA-ENTRY",
            "instruction entries",
            "Every instruction entry of the vendored table that is decoded, and every entry "
            "added for instructions the table lacks, is a constructor of `Entry`, with its "
            "mnemonic, family, effect class, PTX ISA section, modifier slots and operands. The "
            "file is generated from the vendored instruction table by `Tools/isa/gen_lean.py`; "
            "the assignment of entries to families is `Tools/isa/families.py`.",
            source_ref(m)
            + ["the entries added and the corrections made in `Tools/isa/extra.py`"]
            + quotes,
            "An entry's slots are its modifier positions in syntax order; `optional` slots may "
            "be omitted. The mask of a slot has bit `Slot.code s t` set for every choice `t`. "
            "An operand's lanes (number of registers), type token and whether a lane may be the "
            "sink `_` are `Fact`s: a constant, the token of a slot, or a table keyed by the codes "
            "of the slots the fact depends on (base-128 digits in slot order). The effect class "
            "is `event` for an entry with an address operand or one that orders memory, `ctl` "
            "for control flow and `local` otherwise. Excluded table entries (wgmma) have no "
            "constructor. A table entry whose PTX spelling is that of another entry (mapa with a "
            "pointer or an integer address; the `.b8` and `.b16` TMA override tensor sizes) has no "
            "constructor either and decodes as that entry (`ALIASES` in `Tools/isa/families.py`); "
            "an operand whose type differs between the two has no type token. Corrections of the "
            "table: `elect.sync`'s `d` may be the sink, and every `tcgen05.mma` entry with a "
            "`disable-output-lane` vector has a sibling `<name>_nomask` without it, the form of "
            "the ISA's examples. `mapa` is split by its `.space` qualifier: `mapa` (with "
            "`.shared::cluster`) takes a variable `var` or `var+imm` as `a`, and `mapa_generic` "
            "(without `.space`) takes a register. `getctarank` takes a variable as `a`; `mov`'s "
            "`a` may be a variable with an offset (`regvar`); `ld` and `ld_vec` accept the "
            "`.const` space.",
        )
    )
    out.append("\nnamespace PTX.Isa\n\n")
    fams = [f for f in families.FAMILIES if f != "excluded"]
    out.append("/-- The family whose layer translates an entry. -/\ninductive Family where\n")
    for f in fams:
        out.append(f"  /-- {FAMILY_DOC[f].capitalize()}. -/\n  | {f}\n")
    out.append("  deriving DecidableEq, Repr, Inhabited\n\n")
    out.append(
        "/-- How an entry acts: events touch memory or order it, `ctl` changes the program\n"
        "counter, `local` computes registers. -/\n"
        "inductive Effect where\n  | event\n  | ctl\n  | local_\n"
        "  deriving DecidableEq, Repr, Inhabited\n\n"
        "/-- What an operand is: a register (or register group), an address `[...]`, a pointer\n"
        "register, a register or a variable's address `var` or `var+imm` (`var`), a register source\n"
        "that may also be a variable's address `var` or `var+imm` (`regvar`), an immediate in the\n"
        "instruction text, or a label. -/\n"
        "inductive OKind where\n  | reg\n  | addr\n  | ptr\n  | var\n  | regvar\n  | imm\n  | label\n"
        "  deriving DecidableEq, Repr, Inhabited\n\n"
        "/-- The data direction of an operand. -/\n"
        "inductive Role where\n  | r\n  | w\n  | rw\n"
        "  deriving DecidableEq, Repr, Inhabited\n\n"
        "/-- The values an immediate operand may take: none (not an immediate), the sink `_`, one\n"
        "of a list of integers, or any integer constant. -/\n"
        "inductive Imm where\n  | none\n  | sink\n  | choices (values : List Int)\n  | free\n"
        "  deriving DecidableEq, Repr, Inhabited\n\n"
        "/-- A fact of an operand as a function of the modifier codes. -/\n"
        "inductive Fact (α : Type) where\n"
        "  | const (v : α)\n"
        "  /-- The token chosen in slot `k`. -/\n"
        "  | slot (k : Nat)\n"
        "  /-- Rows keyed by the codes of slots `keys`, as base-128 digits. -/\n"
        "  | table (keys : List Nat) (rows : List (Nat × α))\n"
        "  deriving Repr\n\n"
        "/-- One operand of an entry. -/\n"
        "structure OpSpec where\n"
        "  name : String\n  kind : OKind\n  role : Role\n"
        "  /-- Written as a brace-enclosed register group. -/\n"
        "  group : Bool\n"
        "  /-- Whether the grammar asks the predicate-register oracle for this operand. -/\n"
        "  predCheck : Bool\n  imm : Imm\n"
        "  lanes : Fact Nat\n  dtype : Fact (Option Token)\n  sink : Fact Bool\n"
        "  deriving Repr\n\n"
        "/-- Operands as written: one operand, a pipe pair `p|q`, or a composite address\n"
        "`[m0, m1, ...]`. -/\n"
        "inductive OpGroup where\n"
        "  | single (s : OpSpec)\n  | pipe (members : List OpSpec)\n"
        "  | bracket (members : List OpSpec)\n"
        "  deriving Repr\n\n"
        "/-- A modifier position: its slot, whether it may be omitted, and its mask. -/\n"
        "structure SlotSpec where\n  slot : Slot\n  optional : Bool\n  mask : Nat\n"
        "  deriving Repr, Inhabited\n\n"
    )
    out.append("/-- The decoded instruction entries. -/\ninductive Entry where\n")
    for e in m.entries:
        out.append(f"  | {m.entry_id[e['name']]}\n")
    out.append("  deriving DecidableEq, Repr, Inhabited\n\n")

    def per_entry(fn, ty, doc, val):
        out.append(f"/-- {doc} -/\ndef Entry.{fn} : Entry → {ty}\n")
        for e in m.entries:
            lines = val(e)
            pre = f"  | .{m.entry_id[e['name']]} => "
            if isinstance(lines, str):
                lines = [lines]
            first = pre + lines[0]
            if len(first) <= WIDTH and len(lines) == 1:
                out.append(first + "\n")
            else:
                out.append(pre.rstrip() + "\n")
                out.extend(
                    "    " + ln.lstrip() + "\n" if not ln.startswith("    ") else ln + "\n"
                    for ln in lines
                )
        out.append("\n")

    per_entry("mnemonic", "String", "The PTX mnemonic.", lambda e: f'"{e["mnemonic"]}"')
    per_entry("name", "String", "The entry's name in the table.", lambda e: f'"{e["name"]}"')
    per_entry("family", "Family", "The family.", lambda e: "." + e["family"])
    per_entry(
        "effect",
        "Effect",
        "The effect class.",
        lambda e: "." + ("local_" if e["effect"] == "local" else e["effect"]),
    )
    per_entry("section", "String", "The PTX ISA 9.5 section.", lambda e: f'"{e["section"]}"')
    per_entry(
        "prefix",
        "List Token",
        "Mnemonic segments after the first.",
        lambda e: "[" + ", ".join("." + m.tok_id[t] for t in m.spec[e["name"]]["prefix"]) + "]",
    )

    def slots_val(e):
        items = [
            f"⟨.{m.slot_id[s]}, {'true' if o else 'false'}, {mask}⟩"
            for s, o, mask in m.spec[e["name"]]["slots"]
        ]
        return lean_list(items, "    ")

    per_entry("slotSpecs", "List SlotSpec", "The modifier positions in syntax order.", slots_val)

    def ops_val(e):
        lines = ["["]
        groups = m.spec[e["name"]]["groups"]
        for gi, (kind, members) in enumerate(groups):
            tail = "," if gi < len(groups) - 1 else ""
            if kind == "single":
                ls = opspec_lean(m, members[0], "      ")
                ls[0] = "    .single " + ls[0].lstrip()
                ls[-1] += tail
                lines += ls
            else:
                lines.append(f"    .{kind} [")
                for mi, mem in enumerate(members):
                    ls = opspec_lean(m, mem, "        ")
                    ls[0] = "      " + ls[0].lstrip()
                    if mi < len(members) - 1:
                        ls[-1] += ","
                    lines += ls
                lines.append("    ]" + tail)
        lines.append("    ]")
        if len(lines) == 2:
            return "[]"
        return lines

    per_entry("operands", "List OpGroup", "The operands in syntax order.", ops_val)
    out.append(
        "/-- Alternative written orders of the slots: the slot indices in written order, and the\n"
        "inverse permutation. -/\n"
        "def Entry.orders : Entry → List (List Nat × List Nat)\n"
    )
    for e in m.entries:
        orders = m.spec[e["name"]]["orders"]
        if orders:
            items = [f"({lst(p)}, {lst(q)})" for p, q in orders]
            out.append(f"  | .{m.entry_id[e['name']]} => [{', '.join(items)}]\n")
    out.append("  | _ => []\n\n")
    out.append(
        "/-- The slots of an entry with their optional flags. -/\n"
        "def Entry.slots (e : Entry) : List (Slot × Bool) :=\n"
        "  e.slotSpecs.map fun s => (s.slot, s.optional)\n\n"
        "/-- The operand specifications of an entry, in syntax order. -/\n"
        "def Entry.operandSpecs (e : Entry) : List OpSpec :=\n"
        "  e.operands.flatMap fun\n"
        "    | .single s => [s]\n    | .pipe ms => ms\n    | .bracket ms => ms\n\n"
    )
    out.append("end PTX.Isa\n")
    return "".join(out)


def gen_constraint(m):
    out = [header(m, "Constraint")]
    out.append("public import Core.Source.Isa.Entry\n\n@[expose] public section\n\n")
    out.append(
        contract(
            "PROG-ISA-CONSTRAINT",
            "legal modifier combinations",
            "For every decoded entry, the legal combinations of modifier values are a union of "
            "cubes, each cube giving one set of allowed values per slot. The cubes are computed "
            "by `Tools/isa/constraints.py` from the table's `check` function, evaluated over all "
            "slot combinations when the table was vendored, and their union is verified to equal "
            "the legal set exactly. The file is generated by `Tools/isa/gen_lean.py`.",
            source_ref(m),
            "A cube is a list of masks aligned with `Entry.slotSpecs`; bit 0 of a mask allows "
            "the omitted value and bit `Slot.code s t` allows token `t`.",
        )
    )
    out.append("\nnamespace PTX.Isa\n\n")
    out.append("/-- The cubes of legal modifier combinations. -/\n")
    out.append("def Entry.cubes : Entry → List (List Nat)\n")
    for e in m.entries:
        cs = m.spec[e["name"]]["cubes"]
        items = ["[" + ", ".join(map(str, c)) + "]" for c in cs]
        pre = f"  | .{m.entry_id[e['name']]} => "
        one = pre + "[" + ", ".join(items) + "]"
        if len(one) <= WIDTH:
            out.append(one + "\n")
        else:
            out.append(pre.rstrip() + "\n")
            out.extend(ln + "\n" for ln in lean_list(items, "    "))
    out.append("\nend PTX.Isa\n")
    return "".join(out)


GRAMMAR_BODY = r"""
/-- An operand as written, with its table information: the operand's name, kind and data
direction, its type token under the decoded modifiers, and its number of registers. Inside a
pipe pair or a composite address, `op` is the member as written. -/
structure ROpnd where
  name : String
  kind : OKind
  role : Role
  dtype : Option Token
  lanes : Nat
  op : Operand
  deriving Repr

/-- A recognized instruction: its entry, the value of every slot (`none` when omitted) and its
operands. -/
structure Raw where
  entry : Entry
  mods : List (Slot × Option Token)
  opnds : List ROpnd
  deriving Repr

/-- The value of a slot. -/
def Raw.get (r : Raw) (s : Slot) : Option Token :=
  match r.mods.find? (fun m => m.1 == s) with
  | some (_, t) => t
  | none => none

/-- The bytes of a string. Kernel reduction reads a string literal's UTF-8 bytes cheaply and
its characters (`String.toList`) expensively, so the grammar reads bytes. -/
def bytes (s : String) : List Nat := s.toByteArray.data.toList.map (·.toNat)

/-- The tokens of an opcode, from its bytes: its dot-separated segments. -/
def opTokens : List Nat → Nat → List Token → Option (List Token)
  | [], k, acc => (Token.ofKey? k).map fun t => (t :: acc).reverse
  | n :: bs, k, acc =>
    bif Nat.beq n 46 then
      match Token.ofKey? k with
      | some t => opTokens bs 0 (t :: acc)
      | none => none
    else bif Nat.blt 0 n && Nat.blt n 128 then opTokens bs (k * 128 + n) acc else none

/-- Whether bit `c` of `mask` is set. -/
def hasBit (mask c : Nat) : Bool := Nat.beq ((mask >>> c) % 2) 1

/-- The mnemonic segments after the first must follow in order. -/
def stripPrefix : List Token → List Token → Option (List Token)
  | [], ts => some ts
  | p :: ps, t :: ts => bif p == t then stripPrefix ps ts else none
  | _ :: _, [] => none

/-- Take `t` for slot `sp` when it is one of the slot's choices. -/
def takeTok (sp : SlotSpec) (t : Token) (rest : List Token) :
    Option (Option Token × Nat × List Token) :=
  let c := Slot.code sp.slot t
  bif Nat.blt 0 c && hasBit sp.mask c then some (some t, c, rest) else none

/-- The value of one slot from the front of the tokens: a composite of three or two segments,
then a single token, then the omitted value when the slot is optional. -/
def pick (sp : SlotSpec) (ts : List Token) : Option (Option Token × Nat × List Token) :=
  let three := match ts with
    | a :: b :: c :: rest => (Token.comp3? a b c).bind fun t => takeTok sp t rest
    | _ => none
  match three with
  | some r => some r
  | none =>
    let two := match ts with
      | a :: b :: rest => (Token.comp2? a b).bind fun t => takeTok sp t rest
      | _ => none
    match two with
    | some r => some r
    | none =>
      let one := match ts with
        | a :: rest => takeTok sp a rest
        | [] => none
      match one with
      | some r => some r
      | none => bif sp.optional then some (none, 0, ts) else none

/-- Align the tokens with the slots, left to right. -/
def align : List SlotSpec → List Token → Option (List (Option Token) × List Nat × List Token)
  | [], ts => some ([], [], ts)
  | sp :: sps, ts =>
    match pick sp ts with
    | none => none
    | some (v, c, ts') =>
      match align sps ts' with
      | some (vs, cs, r) => some (v :: vs, c :: cs, r)
      | none => none

/-- Whether the codes lie in the cube. -/
def inCube : List Nat → List Nat → Bool
  | m :: ms, c :: cs => hasBit m c && inCube ms cs
  | [], [] => true
  | _, _ => false

/-- The key of a fact table row: the codes of the key slots as base-128 digits. -/
def factKey (codes : List Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | k :: ks, acc => factKey codes ks (acc * 128 + codes.getD k 0)

/-- The row with the given key. -/
def lookupRow {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (k, v) :: rs, key => bif Nat.beq k key then some v else lookupRow rs key

/-- The decoded modifiers of an instruction and the predicate-register oracle, as the operand
rules need them. -/
structure Ctx where
  isPred : String → Bool
  toks : List (Option Token)
  codes : List Nat

/-- The value of a fact under the decoded modifiers. -/
def Fact.eval {α : Type} (f : Fact α) (x : Ctx) (slotv : Option Token → Option α) :
    Option α :=
  match f with
  | .const v => some v
  | .slot k => slotv (x.toks.getD k none)
  | .table ks rows => lookupRow rows (factKey x.codes ks 0)

def OpSpec.lanesIn (s : OpSpec) (x : Ctx) : Nat :=
  (s.lanes.eval x fun _ => none).getD 0

def OpSpec.dtypeIn (s : OpSpec) (x : Ctx) : Option Token :=
  match s.dtype.eval x fun t => some t with
  | some d => d
  | none => none

def OpSpec.sinkIn (s : OpSpec) (x : Ctx) : Bool :=
  (s.sink.eval x fun _ => none).getD false

/-- The value of an integer literal from its bytes: hexadecimal, binary, octal or decimal digits
(§4.5.1), an optional `U` suffix and an optional leading minus. -/
def digitsVal (base : Nat) : List Nat → Nat → Option Nat
  | [], acc => some acc
  | n :: cs, acc =>
    let d : Option Nat :=
      bif Nat.ble 48 n && Nat.blt n 58 then some (n - 48)
      else bif Nat.ble 97 n && Nat.blt n 103 then some (n - 87)
      else bif Nat.ble 65 n && Nat.blt n 71 then some (n - 55)
      else none
    match d with
    | some v => bif Nat.blt v base then digitsVal base cs (acc * base + v) else none
    | none => none

def natVal : List Nat → Option Nat
  | 48 :: 120 :: c :: cs | 48 :: 88 :: c :: cs => digitsVal 16 (c :: cs) 0
  | 48 :: 98 :: c :: cs | 48 :: 66 :: c :: cs => digitsVal 2 (c :: cs) 0
  | 48 :: c :: cs => digitsVal 8 (c :: cs) 0
  | c :: cs => digitsVal 10 (c :: cs) 0
  | [] => none

def litVal (text : String) : Option Int :=
  let cs := bytes text
  let cs := bif cs.getLast?.any (Nat.beq · 85) then cs.dropLast else cs
  match cs with
  | 45 :: ds => (natVal ds).map fun v => -(v : Int)
  | ds => (natVal ds).map fun v => (v : Int)

/-- An immediate operand as written. -/
def immOk : Imm → Operand → Bool
  | .sink, .sink => true
  | .choices vs, .literal t =>
    match litVal t with
    | some v => vs.any (· == v)
    | none => false
  | .free, .literal _ => true
  | _, _ => false

/-- One register of an operand: a register or a name (a register declared without `%`, or for
a source a variable's address); for a source also a constant, and a negated register when the
operand is a predicate; the sink `_` where the table allows it. When `check` is set, the name is
a predicate register exactly when the operand's type is `.pred`, and a predicate operand takes no
constant (cp.async's `ignore-src` is a "non-immediate predicate argument"). -/
def elemOk (isPred : String → Bool) (check : Bool) (role : Role) (pred sink : Bool) :
    Operand → Bool
  | .register n | .symbol n => !check || isPred n == pred
  | .sink => sink
  | .literal _ => role == .r && !(check && pred)
  | .negate (.register _) | .negate (.symbol _) => role == .r && pred
  | _ => false

/-- The sign of an address offset. -/
def signOk (sign : String) : Bool :=
  match bytes sign with
  | [43] | [45] => true
  | _ => false

/-- The inside of an address operand: a register, a symbol, a constant, or a register or symbol
with a constant offset. -/
def addrOk : Operand → Bool
  | .register _ | .symbol _ | .literal _ => true
  | .offset sign (.register _) (.literal _) | .offset sign (.symbol _) (.literal _) =>
    signOk sign
  | _ => false

/-- Match one operand; `inner` for a member of a pipe pair or of a composite address, where an
address member is a bare register or symbol. A scalar register operand may be written as a
brace list of that one register, `{ %r }`, which stands for the register. -/
def matchOne (x : Ctx) (inner : Bool) (s : OpSpec) (o₀ : Operand) : Option ROpnd :=
  let o := match s.kind, s.group, o₀ with
    | .reg, false, .vector [c] => c
    | _, _, _ => o₀
  let n := s.lanesIn x
  let d := s.dtypeIn x
  let ok : Bool := match s.kind with
    | .reg =>
      bif s.group then
        match o with
        | .vector cs =>
          Nat.beq cs.length n &&
            cs.all (elemOk x.isPred s.predCheck s.role (d == some .pred) (s.sinkIn x))
        | _ => false
      else elemOk x.isPred s.predCheck s.role (d == some .pred) (s.sinkIn x) o
    | .addr =>
      bif inner then
        match o with
        | .register _ | .symbol _ => true
        | _ => false
      else
        match o with
        | .address [a] => addrOk a
        | _ => false
    | .ptr =>
      match o with
      | .register _ | .symbol _ => true
      | _ => false
    | .var =>
      match o with
      | .register _ | .symbol _ => true
      | .offset sign (.symbol _) (.literal _) => signOk sign
      | _ => false
    | .regvar =>
      elemOk x.isPred s.predCheck s.role (d == some .pred) (s.sinkIn x) o ||
        match o with
        | .offset sign (.symbol _) (.literal _) => signOk sign
        | _ => false
    | .imm => immOk s.imm o
    | .label =>
      match o with
      | .symbol _ => true
      | _ => false
  bif ok then some ⟨s.name, s.kind, s.role, d, n, o⟩ else none

/-- Match the members of a pipe pair or a composite address. -/
def matchMembers (x : Ctx) : List OpSpec → List Operand → Option (List ROpnd)
  | [], [] => some []
  | s :: ss, o :: os =>
    match matchOne x true s o, matchMembers x ss os with
    | some r, some rs => some (r :: rs)
    | _, _ => none
  | _, _ => none

/-- Match the written operands against the operand groups; an operand with no registers under
the decoded modifiers is absent. -/
def matchOps (x : Ctx) : List OpGroup → List Operand → Option (List ROpnd)
  | [], [] => some []
  | .single s :: gs, os =>
    bif Nat.beq (s.lanesIn x) 0 then matchOps x gs os
    else match os with
      | o :: os' =>
        match matchOne x false s o, matchOps x gs os' with
        | some r, some rs => some (r :: rs)
        | _, _ => none
      | [] => none
  | .pipe ms :: gs, .pair cs :: os' =>
    match matchMembers x ms cs, matchOps x gs os' with
    | some r, some rs => some (r ++ rs)
    | _, _ => none
  | .bracket ms :: gs, .address cs :: os' =>
    match matchMembers x ms cs, matchOps x gs os' with
    | some r, some rs => some (r ++ rs)
    | _, _ => none
  | _, _ => none

/-- The values and codes of the slots when the tokens align with `sps` and lie in a cube;
`inv` reorders values aligned in an alternative written order to the canonical order. -/
def slotsOk (e : Entry) (ts : List Token) (sps : List SlotSpec) (inv : Option (List Nat)) :
    Option (List (Option Token) × List Nat) :=
  match align sps ts with
  | some (toks, codes, []) =>
    let (toks, codes) := match inv with
      | some q => (q.map fun i => toks.getD i none, q.map fun i => codes.getD i 0)
      | none => (toks, codes)
    bif e.cubes.any fun c => inCube c codes then some (toks, codes) else none
  | _ => none

/-- The first alternative order in which the slots are recognized. -/
def slotsAlt (e : Entry) (ts : List Token) :
    List (List Nat × List Nat) → Option (List (Option Token) × List Nat)
  | [] => none
  | (p, q) :: rest =>
    match slotsOk e ts (p.map fun k => e.slotSpecs.getD k default) (some q) with
    | some r => some r
    | none => slotsAlt e ts rest

/-- Recognize an instruction as one entry, or fail. -/
def tryEntry (isPred : String → Bool) (os : List Operand) (ts : List Token) (e : Entry) :
    Option Raw :=
  match stripPrefix e.prefix ts with
  | none => none
  | some ts =>
    let slots := match slotsOk e ts e.slotSpecs none with
      | some r => some r
      | none => slotsAlt e ts e.orders
    match slots with
    | some (toks, codes) =>
      match matchOps ⟨isPred, toks, codes⟩ e.operands os with
      | some opnds => some ⟨e, (e.slotSpecs.map (·.slot)).zip toks, opnds⟩
      | none => none
    | none => none

/-- Recognize an instruction: split the opcode at dots, dispatch on the mnemonic's first
segment, and require exactly one entry to accept the modifiers and operands. `isPred n` says
whether the name `n` is a predicate register. -/
def Grammar.parse (isPred : String → Bool) (op : String) (os : List Operand) :
    Except String Raw :=
  match opTokens (bytes op) 0 [] with
  | some (h :: ts) =>
    match excluded? h with
    | some reason => .error reason
    | none =>
      match (candidates h).filterMap (tryEntry isPred os ts) with
      | [r] => .ok r
      | [] => .error ("no instruction entry accepts " ++ op)
      | _ => .error ("several instruction entries accept " ++ op)
  | _ => .error ("unknown opcode token in " ++ op)
"""


def gen_grammar(m):
    out = [header(m, "Grammar")]
    out.append("public import Core.Source.Isa.Constraint\n\n@[expose] public section\n\n")
    out.append(
        contract(
            "PROG-ISA-GRAMMAR",
            "recognizing an instruction",
            "`Grammar.parse` recognizes a PTX instruction, given its opcode string and its "
            "operands as written, as one instruction entry with the value of every modifier slot "
            "and its operands; when no entry or more than one entry accepts the instruction it "
            "fails, so decoding is never ambiguous. The dispatch tables are generated from the "
            "vendored instruction table by `Tools/isa/gen_lean.py`.",
            source_ref(m)
            + [
                'PTX ISA 9.5 §6.4.3 (Vectors as Operands): "A brace-enclosed list is used for '
                'pattern matching to pull apart vectors."'
            ],
            "The opcode is split at dots; the first segment selects the candidate entries "
            "(`candidates`), a wgmma mnemonic fails with its reason (`excluded?`). For each "
            "candidate the remaining segments must follow the mnemonic's own segments and then "
            "align with the entry's slots left to right, each slot taking a composite of three "
            "or two segments, a single token, or nothing when it is optional. PTX writes "
            "qualifiers in syntax order; the one exception is `.cta_group` and "
            "`.level::cache_hint` of cp.async.bulk.tensor, which ptxas accepts in either order, "
            "so an entry with both slots is also tried with the two swapped (`Entry.orders`). "
            "The slot values must lie in one cube of `Entry.cubes`. The operands must match the "
            "entry's operand groups: a register group is a vector of exactly its lanes, `_` only "
            "where the table allows the sink, `p|q` pairs and composite addresses `[m0, ...]` "
            "member by member, an address `[r]`, `[sym]`, `[imm]`, `[r+imm]` or `[r-imm]`, an "
            "operand with no registers under the modifiers absent. A register operand may be "
            "written as a name without `%`, and a scalar register operand as a brace list of that one "
            "register, `{ %r }`, which stands for the register (a reading: the manual defines "
            "the brace list only for vectors, and ptxas accepts the one-element list). Register "
            "names and widths are left to the family "
            "layer, which resolves them with the decoder's environment, with one exception: "
            "cp.async's `src-size` and `ignore-src` are told apart only by whether the register "
            "is a predicate, so for operands with `predCheck` the grammar asks the caller's "
            "oracle `isPred`. Strings are read through their UTF-8 bytes, which kernel reduction "
            "handles much faster than `String.toList`.",
        )
    )
    out.append("\nnamespace PTX.Isa\nopen PTX.Syntax\n\n")
    out.append("/-- The entries whose mnemonic starts with a token. -/\n")
    out.append("def candidates : Token → List Entry\n")
    for h in sorted(m.heads):
        items = ["." + m.entry_id[n] for n in m.heads[h]]
        out.extend(ln + "\n" for ln in lean_list(items, "  ", f"| .{m.tok_id[h]} => "))
    out.append("  | _ => []\n\n")
    out.append("/-- Mnemonics outside the scope of the decoder, with the reason. -/\n")
    out.append("def excluded? : Token → Option String\n")
    for h, r in sorted(m.excluded_heads.items()):
        out.append(f'  | .{m.tok_id[h]} => some "{r}"\n')
    out.append("  | _ => none\n")
    out.append(GRAMMAR_BODY)
    out.append("\nend PTX.Isa\n")
    return "".join(out)


def fit(text):
    """Break every code line longer than WIDTH after a comma, continuing 4 columns deeper."""
    out = []
    for line in text.split("\n"):
        cont = " " * (len(line) - len(line.lstrip()) + 4)
        while len(line) > WIDTH:
            cut = line.rfind(", ", 0, WIDTH - 1)
            if cut < len(cont):
                raise ValueError(f"cannot fit line: {line.strip()[:90]}")
            out.append(line[: cut + 1])
            line = cont + line[cut + 2 :]
        out.append(line)
    return "\n".join(out)


def generate(m=None):
    """Generated files by path relative to the repository root."""
    import crosscheck

    m = m or build_model()
    return {
        "Core/Source/Isa/Token.lean": fit(gen_token(m)),
        "Core/Source/Isa/Entry.lean": fit(gen_entry(m)),
        "Core/Source/Isa/Constraint.lean": fit(gen_constraint(m)),
        "Core/Source/Isa/Grammar.lean": fit(gen_grammar(m)),
        "Tests/Source/IsaCrossCheck.lean": crosscheck.lean_test(crosscheck.prepare(m)),
    }


def checks(m):
    """The partition of entries into families, the aliases, and the cubes and fact tables."""
    table = load()
    return (
        families.check_partition(table, m.final)
        + families.check_aliases(m.final)
        + constraints.verify_all([e for e in m.final if not e.get("alias_of")])
    )


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument("--check", action="store_true")
    args = cli.parse_args()
    m = build_model()
    errors = checks(m)
    if errors:
        print("\n".join(errors))
        sys.exit(1)
    files = generate(m)
    stale = []
    for name, text in files.items():
        path = ROOT / name
        if args.check:
            if not path.exists() or path.read_text() != text:
                stale.append(name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    if stale:
        print("stale generated files: " + ", ".join(stale) + " (run Tools/isa/gen_lean.py)")
        sys.exit(1)


if __name__ == "__main__":
    main()
