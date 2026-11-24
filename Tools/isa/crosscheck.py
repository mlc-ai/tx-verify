# SPDX-License-Identifier: Apache-2.0
"""Python implementation of the generated grammar, and its cross-check against the Lean one.

`parse(m, opcode, operands)` mirrors `PTX.Isa.Grammar.parse` (Core/Source/Isa/Grammar.lean) on
the model of `gen_lean.build_model`: operands are `parse_ptx.Operand` trees. Both sides print a
recognized instruction in one canonical line (`show`), so the check compares text.

    python3 Tools/isa/crosscheck.py                 # the repository's ten kernels
    python3 Tools/isa/crosscheck.py --corpus        # also the survey corpus ($TXVERIFY_SURVEY_INPUTS)
    python3 Tools/isa/crosscheck.py --no-lean       # Python side only

Inputs checked:
* every distinct instruction form of the corpus (register and symbol names are replaced by
  canonical names that keep only whether the name is a predicate register, which is all the
  grammar asks of a name);
* for every cube of every entry, one synthesized instruction that must be recognized as that
  entry with that combination, and for each slot value adjacent to the cube that makes the
  combination illegal, one synthesized instruction that must not be recognized as that entry
  with that combination.

The Lean side reads the instructions from a text file at run time (a scratch Lean file under
`--work`, by default `.lake/isa-crosscheck`, evaluates `Grammar.parse` on each line), so no
large Lean data has to be elaborated. The Lean side needs current `.olean` files of
`Core.Source.Isa.Grammar` (`Tools/build.sh Core.Source.Isa.Grammar`).
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "Tools"))
import constraints  # noqa: E402
import gen_lean  # noqa: E402
from parse_ptx import Operand, parse as parse_ptx  # noqa: E402

# Scratch directory of the Lean side (the driver file, its input and output).
DEFAULT_WORK = ROOT / ".lake" / "isa-crosscheck"
# The survey corpus of `--corpus`: the directory named by the environment variable
# TXVERIFY_SURVEY_INPUTS holds an `inputs.py` whose `INPUTS` maps names to PTX files. Without the
# variable, `--corpus` adds nothing.
SURVEY_ENV = "TXVERIFY_SURVEY_INPUTS"

# ----------------------------------------------------------------------------- grammar


class Error(Exception):
    pass


def op_tokens(m, opcode):
    toks = []
    for seg in opcode.split("."):
        if seg not in m.tok_id or "." in seg:
            return None
        toks.append(seg)
    return toks


def has_bit(mask, c):
    return (mask >> c) & 1 == 1


def take_tok(m, slot, mask, t, rest):
    c = gen_lean.code(m, slot, t) if t in m.slot_union[slot] else 0
    if c > 0 and has_bit(mask, c):
        return (t, c, rest)
    return None


def pick(m, sp, ts):
    slot, optional, mask = sp
    for n in (3, 2):
        if len(ts) >= n:
            comp = m.composites.get(tuple(ts[:n]))
            if comp is not None:
                r = take_tok(m, slot, mask, comp, ts[n:])
                if r:
                    return r
    if ts:
        r = take_tok(m, slot, mask, ts[0], ts[1:])
        if r:
            return r
    if optional:
        return ("", 0, ts)
    return None


def align(m, slots, ts):
    vals, codes = [], []
    for sp in slots:
        r = pick(m, sp, ts)
        if r is None:
            return None
        v, c, ts = r
        vals.append(v)
        codes.append(c)
    return vals, codes, ts


def in_cube(cube, codes):
    return all(has_bit(mk, c) for mk, c in zip(cube, codes, strict=True))


def fact_eval(f, vals, codes):
    if f[0] == "const":
        return f[1]
    if f[0] == "slot":
        return vals[f[1]] or None
    _, ks, rows = f
    k = 0
    for i in ks:
        k = k * gen_lean.FACT_BASE + codes[i]
    for rk, v in rows:
        if rk == k:
            return v
    return None


def lit_value(text):
    try:
        return gen_lean.lit_value(text)
    except ValueError:
        return None


def imm_ok(imm, o):
    if imm[0] == "sink":
        return o.kind == "sink"
    if imm[0] == "choices":
        return o.kind == "literal" and lit_value(o.text) in imm[1]
    if imm[0] == "free":
        return o.kind == "literal"
    return False


def is_pred(name):
    """The predicate-register oracle of the cross-check: canonical names (see `canonical`)."""
    return name in ("%p", "p")


def elem_ok(check, role, pred, sink, o):
    if o.kind in ("register", "symbol"):
        return not check or is_pred(o.text) == pred
    if o.kind == "sink":
        return sink
    if o.kind == "literal":
        return role == "r" and not (check and pred)
    if o.kind == "not":
        return role == "r" and pred and o.children[0].kind in ("register", "symbol")
    return False


def addr_ok(o):
    if o.kind in ("register", "symbol", "literal"):
        return True
    if o.kind == "offset":
        b, lit = o.children
        return o.text in ("+", "-") and b.kind in ("register", "symbol") and lit.kind == "literal"
    return False


def match_one(s, vals, codes, inner, o):
    n = fact_eval(s["lanes"], vals, codes) or 0
    d = fact_eval(s["dtype"], vals, codes)
    sink = bool(fact_eval(s["sink"], vals, codes))
    k = s["kind"]
    if k in ("reg", "regvar"):
        if s["group"]:
            ok = o.kind == "vector" and len(o.children) == n
            ok = ok and all(
                elem_ok(s["pred_check"], s["rw"], d == "pred", sink, c) for c in o.children
            )
        else:
            # A scalar register operand may be written as a brace list of that one register.
            if k == "reg" and o.kind == "vector" and len(o.children) == 1:
                o = o.children[0]
            ok = elem_ok(s["pred_check"], s["rw"], d == "pred", sink, o)
        if k == "regvar":
            ok = ok or (
                o.kind == "offset"
                and o.text in ("+", "-")
                and o.children[0].kind == "symbol"
                and o.children[1].kind == "literal"
            )
    elif k == "addr":
        if inner:
            ok = o.kind in ("register", "symbol")
        else:
            ok = o.kind == "address" and len(o.children) == 1 and addr_ok(o.children[0])
    elif k == "ptr":
        ok = o.kind in ("register", "symbol")
    elif k == "var":
        ok = o.kind in ("register", "symbol") or (
            o.kind == "offset"
            and o.text in ("+", "-")
            and o.children[0].kind == "symbol"
            and o.children[1].kind == "literal"
        )
    elif k == "imm":
        ok = imm_ok(s["imm"], o)
    elif k == "label":
        ok = o.kind == "symbol"
    else:
        ok = False
    return (s["name"], k, s["rw"], d, n, o) if ok else None


def match_ops(groups, vals, codes, os_):
    out = []
    os_ = list(os_)
    for kind, members in groups:
        if kind == "single":
            s = members[0]
            if (fact_eval(s["lanes"], vals, codes) or 0) == 0:
                continue
            if not os_:
                return None
            r = match_one(s, vals, codes, False, os_.pop(0))
            if r is None:
                return None
            out.append(r)
        else:
            want = "pair" if kind == "pipe" else "address"
            if not os_ or os_[0].kind != want:
                return None
            cs = os_.pop(0).children
            if len(cs) != len(members):
                return None
            for s, c in zip(members, cs, strict=True):
                r = match_one(s, vals, codes, True, c)
                if r is None:
                    return None
                out.append(r)
    return out if not os_ else None


def slots_ok(m, spec, ts, sps, inv):
    r = align(m, sps, ts)
    if r is None or r[2]:
        return None
    vals, codes, _ = r
    if inv is not None:
        vals = [vals[i] for i in inv]
        codes = [codes[i] for i in inv]
    if not any(in_cube(c, codes) for c in spec["cubes"]):
        return None
    return vals, codes


def try_entry(m, e, ts, os_):
    spec = m.spec[e["name"]]
    pre = spec["prefix"]
    if ts[: len(pre)] != pre:
        return None
    ts = ts[len(pre) :]
    r = slots_ok(m, spec, ts, spec["slots"], None)
    for perm, inv in spec["orders"]:
        if r is not None:
            break
        r = slots_ok(m, spec, ts, [spec["slots"][k] for k in perm], inv)
    if r is None:
        return None
    vals, codes = r
    ops = match_ops(spec["groups"], vals, codes, os_)
    if ops is None:
        return None
    return (e["name"], [(s[0], v) for s, v in zip(e["slots"], vals, strict=True)], ops)


def parse(m, opcode, operands):
    ts = op_tokens(m, opcode)
    if not ts:
        raise Error("unknown opcode token")
    h = ts[0]
    if h in m.excluded_heads:
        raise Error(m.excluded_heads[h])
    by_name = m.by_name
    hits = [r for n in m.heads.get(h, []) if (r := try_entry(m, by_name[n], ts[1:], operands))]
    if len(hits) != 1:
        raise Error("no entry" if not hits else "several entries")
    return hits[0]


def prepare(m):
    m.by_name = {e["name"]: e for e in m.entries + m.aliases}
    return m


# ----------------------------------------------------------------------------- printing


def enc(o):
    """The line encoding of an operand, read back by the Lean side."""
    k = o.kind
    if k == "register":
        return "r" + o.text
    if k == "symbol":
        return "s" + o.text
    if k == "literal":
        return "l" + o.text
    if k == "sink":
        return "_"
    if k in ("address", "vector", "pair"):
        return (
            {"address": "a", "vector": "v", "pair": "p"}[k]
            + "("
            + ",".join(enc(c) for c in o.children)
            + ")"
        )
    if k == "not":
        return "n(" + enc(o.children[0]) + ")"
    if k == "offset":
        return "o" + o.text + "(" + enc(o.children[0]) + "," + enc(o.children[1]) + ")"
    raise ValueError(k)


def show(m, result):
    if isinstance(result, Error):
        return "err"
    name, mods, ops = result
    out = ["ok", m.entry_id[name]]
    for slot, v in mods:
        out.append(f"{m.slot_id[slot]}={m.tok_id[v] if v else '-'}")
    for n, k, r, d, lanes, o in ops:
        dt = m.tok_id[d] if d else "-"
        out.append(f"{n}:{k}:{r}:{dt}:{lanes}:{enc(o)}")
    return " ".join(out)


def run(m, opcode, ops):
    try:
        return parse(m, opcode, ops)
    except Error as err:
        return err


# ----------------------------------------------------------------------------- inputs


def corpus_files(survey):
    files = {p.parent.name: p for p in sorted((ROOT / "Kernels").glob("*/*.ptx"))}
    survey_dir = os.environ.get(SURVEY_ENV)
    if survey and survey_dir:
        sys.path.insert(0, survey_dir)
        from inputs import INPUTS

        for k, v in INPUTS.items():
            if Path(v).exists():
                files["survey:" + k] = Path(v)
    return files


PARSER_NOTES = {}


def parse_file(path):
    """Parse a PTX file with the repository's parser, falling back to the text with `+ -n`
    offsets written `-n`."""
    import re

    text = path.read_text()
    try:
        return parse_ptx(text)
    except ValueError as err:
        first = err
    prog = parse_ptx(re.sub(r"\+\s*-\s*(?=\d)", "-", text))
    PARSER_NOTES[str(path)] = f"parsed after writing '+ -n' offsets as '-n' ({first})"
    return prog


def instructions(path):
    """(opcode, canonical operands) of every instruction of every function of a PTX file."""
    prog = parse_file(path)
    out = []

    def walk(stmts, preds):
        for s in stmts:
            if s.kind == "scope":
                walk(s.body, preds)
            elif s.kind == "instruction":
                out.append((s.opcode, [canonical(o, preds) for o in s.operands]))

    for f in prog.functions:
        preds = set()
        collect_preds(f.body, preds)
        walk(f.body, preds)
    return out


def collect_preds(stmts, preds):
    """Names declared `.reg .pred`: plain names, and `pre<n>` as the stem `pre` followed by `*`."""
    for s in stmts:
        if s.kind == "scope":
            collect_preds(s.body, preds)
        elif s.kind == "declaration" and s.tokens[:2] == [".reg", ".pred"]:
            t = s.tokens[2:]
            if len(t) == 4 and t[1] == "<":
                preds.add(t[0] + "*")
            else:
                preds.update(x for x in t if x != ",")


def pred_name(name, preds):
    if name in preds:
        return True
    stem = name.rstrip("0123456789")
    return stem != name and stem + "*" in preds


def canonical(o, preds):
    """Replace names, which the grammar does not read, by fixed ones that keep whether the name
    is a predicate register."""
    if o.kind == "register":
        return Operand("register", "%p" if pred_name(o.text, preds) else "%r")
    if o.kind == "symbol":
        return Operand("symbol", "p" if pred_name(o.text, preds) else "s")
    return Operand(o.kind, o.text, [canonical(c, preds) for c in o.children])


def synth_operands(m, e, combo):
    """Written operands for a legal combination: registers, vectors of the right length, `[r]`
    addresses, the first allowed immediate, labels."""
    if e.get("alias_of"):
        c = m.by_name[e["alias_of"]]
        mods = dict(zip([s[0] for s in e["slots"]], combo, strict=True))
        return synth_operands(m, c, tuple(mods.get(s[0], "") for s in c["slots"]))
    spec = m.spec[e["name"]]
    codes = [gen_lean.code(m, s[0], v) for s, v in zip(e["slots"], combo, strict=True)]
    vals = list(combo)

    def one(s, inner):
        n = fact_eval(s["lanes"], vals, codes) or 0
        k = s["kind"]
        if k in ("reg", "regvar"):
            d = fact_eval(s["dtype"], vals, codes)
            r = Operand("register", "%p" if d == "pred" else "%r")
            if s["group"]:
                return Operand("vector", children=[r] * n)
            return r
        if k == "addr":
            r = Operand("register", "%r")
            return r if inner else Operand("address", children=[r])
        if k in ("ptr", "var"):
            return Operand("register", "%r")
        if k == "imm":
            imm = s["imm"]
            if imm[0] == "sink":
                return Operand("sink", "_")
            if imm[0] == "choices":
                return Operand("literal", str(imm[1][0]))
            return Operand("literal", "0")
        return Operand("symbol", "L")

    out = []
    for kind, members in spec["groups"]:
        if kind == "single":
            s = members[0]
            if (fact_eval(s["lanes"], vals, codes) or 0) == 0:
                continue
            out.append(one(s, False))
        else:
            out.append(
                Operand(
                    "pair" if kind == "pipe" else "address",
                    children=[one(s, True) for s in members],
                )
            )
    return out


def opcode_of(e, combo):
    return ".".join([e["mnemonic"], *[t for t in combo if t]])


def synthesized(m):
    """(positives, negatives): lists of (entry name, combo, opcode, operands). An alias entry's
    positives expect its canonical entry, with the alias's slot values."""
    pos, neg = [], []
    for e in m.entries + m.aliases:
        legal = set(e["variants"])
        doms = constraints.domains(e)
        for cube in constraints.cubes(e):
            rep = tuple(sorted(s)[0] for s in cube)
            pos.append((e["name"], rep, opcode_of(e, rep), synth_operands(m, e, rep)))
            if e.get("alias_of"):
                continue
            for k, dom in enumerate(doms):
                for v in dom:
                    if v in cube[k]:
                        continue
                    bad = rep[:k] + (v,) + rep[k + 1 :]
                    if bad in legal:
                        continue
                    neg.append((e["name"], bad, opcode_of(e, bad), synth_operands(m, e, rep)))
    return pos, neg


# ----------------------------------------------------------------------------- Lean test

# Corpus instructions of the repository's kernels in the committed Lean test, by opcode: one
# of each shape the grammar handles specially.
TEST_CORPUS = [
    "mov.b64",  # a parameter symbol as a source
    "shfl.sync.idx.b32",  # a `d|p` pipe pair
    "elect.sync",  # `_|p`: the sink allowed by the elect.sync override
    "cp.async.bulk.tensor.4d.shared::cluster.global.tile.mbarrier::complete_tx::bytes"
    ".L2::cache_hint.cta_group::2",  # `.cta_group` written after `.L2::cache_hint`
    "tcgen05.mma.cta_group::2.kind::f16",  # without the lane mask
    "ld.param.b64",  # an entry of extra.py
    "bra.uni",
    "mapa.shared::cluster.u32",
    "st.shared.v4.u32",
]


# Instructions for the corrections of the first review, with the entry that must recognize
# each (`None`: no entry). Register names are canonical: `%p` is a predicate register.
REVIEW_CASES = [
    # an integer src-size, never the non-immediate predicate ignore-src
    ("cp.async.ca.shared.global [%r], [%r], 16, 4", "cp_async_ca_src_size"),
    ("cp.async.ca.shared.global [%r], [%r], 16, %p", "cp_async_ca_ignore_src"),
    # .v4 with a 64-bit element only in the global space
    ("ld.param.v4.u64 {%r, %r, %r, %r}, [p]", None),
    ("ld.param.v4.u32 {%r, %r, %r, %r}, [p]", "ld_param_vec"),
    # .weak and .param{::entry, ::func}
    ("ld.param::entry.u32 %r, [p]", "ld_param"),
    ("ld.weak.param.u32 %r, [p+8]", "ld_param"),
    ("ld.param::func.v2.b32 {%r, %r}, [p]", "ld_param_vec"),
    # the .u32 size of cvta and mapa, and var or var+imm sources
    ("cvta.to.shared.u32 %r, %r", "cvta"),
    ("cvta.shared.u64 %r, As+4", "cvta_generic"),
    ("cvta.shared.u32 %r, As", "cvta_generic"),
    ("mapa.u32 %r, %r, %r", "mapa_generic"),
    ("mapa.shared::cluster.u32 %r, sh+4, %r", "mapa"),
    # without `.space`, `a` is a register (§9.7.10.26)
    ("mapa.u32 %r, sh+4, %r", None),
    ("mapa.u64 %r, sh, %r", "mapa_generic"),
    # variable sources of mov (§9.7.10.3) and getctarank (§9.7.10.27)
    ("mov.u32 %r, sh+4", "mov"),
    ("mov.u32 %r, sh", "mov"),
    ("mov.u32 %r, 4", "mov"),
    ("getctarank.shared::cluster.u64 %r, sh+4", "getctarank"),
    ("getctarank.u64 %r, sh+4", None),
    # `.const` of ld's `.ss` (§9.7.10.8)
    ("ld.const.u32 %r, [p+4]", "ld"),
    ("ld.const.v2.u32 {%r, %r}, [p]", "ld_vec"),
    # forms of the previous decoder that the table lacks
    ("cp.async.bulk.wait_group.sync_restrict::proxy::async 2", "cp_async_bulk_wait_group"),
    ("tcgen05.mma.ws.cta_group::1.kind::f16 [%r], %r, %r, %r, 1", "tcgen05_mma_ws_ss_nozcm"),
    ("tcgen05.mma.ws.cta_group::1.kind::i8 [%r], [%r], %r, %r, %p", "tcgen05_mma_ws_ts_nozcm"),
]


def instruction_of(text):
    """(opcode, operands) of one instruction written without the semicolon."""
    from parse_ptx import parse_operand, split_top, tokenize

    toks = [t.text for t in tokenize(text)]
    ops = [parse_operand(p) for p in split_top(toks[1:], ",")] if toks[1:] else []
    return toks[0], ops


def review_failures(m):
    """The review cases the Python grammar gets wrong."""
    out = []
    for text, want in REVIEW_CASES:
        r = run(m, *instruction_of(text))
        got = None if isinstance(r, Error) else r[0]
        if got != want:
            out.append(f"{text}: expected {want}, got {got} ({r})")
    return out


def lean_str(t):
    return json.dumps(t, ensure_ascii=False)


def lean_operand(o):
    if o.kind in ("register", "symbol", "literal"):
        return f"(.{o.kind} {lean_str(o.text)})"
    if o.kind == "sink":
        return ".sink"
    if o.kind in ("address", "vector", "pair"):
        return f"(.{o.kind} [" + ", ".join(lean_operand(c) for c in o.children) + "])"
    if o.kind == "not":
        return f"(.negate {lean_operand(o.children[0])})"
    return (
        f"(.offset {lean_str(o.text)} {lean_operand(o.children[0])} {lean_operand(o.children[1])})"
    )


def lean_opcode(opcode):
    """An opcode string literal, as a concatenation of pieces when it is long."""
    pieces, cur = [], ""
    for seg in opcode.split("."):
        nxt = seg if not cur else cur + "." + seg
        if len(nxt) > 80 and cur:
            pieces.append(cur + ".")
            cur = seg
        else:
            cur = nxt
    pieces.append(cur)
    if len(pieces) == 1:
        return lean_str(opcode)
    return "(" + " ++\n    ".join(lean_str(p) for p in pieces) + ")"


def lean_summary(m, r):
    if isinstance(r, Error):
        return "none"
    name, mods, ops = r
    ms = ", ".join(f"(.{m.slot_id[s]}, {'some .' + m.tok_id[v] if v else 'none'})" for s, v in mods)
    os_ = ", ".join(
        f"({lean_str(n)}, {'some .' + m.tok_id[d] if d else 'none'}, {lanes})"
        for n, _, _, d, lanes, _ in ops
    )
    return f"some (.{m.entry_id[name]}, [{ms}], [{os_}])"


def lean_test(m):
    """The committed Lean test: one synthesized positive and one negative per family, and the
    corpus instructions of `TEST_CORPUS`, each with the summary the Python grammar gives."""
    import gen_lean

    pos, neg = synthesized(m)
    cases = []
    seen_pos, seen_neg = set(), set()
    fam = {e["name"]: e["family"] for e in m.entries + m.aliases}
    for name, combo, opcode, ops in pos:
        if fam[name] not in seen_pos and not m.by_name[name].get("alias_of"):
            seen_pos.add(fam[name])
            cases.append(("synthesized, " + fam[name], opcode, ops, True))
    for name, combo, opcode, ops in neg:
        if fam[name] not in seen_neg:
            seen_neg.add(fam[name])
            cases.append((f"illegal combination of {name}", opcode, ops, False))
    found = {}
    for path in corpus_files(False).values():
        for opcode, ops in instructions(path):
            if opcode in TEST_CORPUS and opcode not in found:
                found[opcode] = ops
    for opcode in TEST_CORPUS:
        cases.append(("corpus", opcode, found[opcode], True))
    for text, want in REVIEW_CASES:
        opcode, ops = instruction_of(text)
        cases.append((f"review: {want or 'rejected'}", opcode, ops, want is not None))
    cases.append(("out of scope", "wgmma.fence.sync.aligned", [], False))
    out = [
        "-- SPDX-License-Identifier: Apache-2.0",
        "",
        "-- Generated by Tools/isa/gen_lean.py. Do not edit.",
        "module",
        "",
        "public import Core.Source.Isa.Grammar",
        "public meta import Core.Source.Isa.Grammar",
        "",
        "/-! The grammar layer on a fixed sample: one synthesized instruction per family that must",
        "be recognized, one with an illegal modifier combination per family that must not be",
        "recognized as that combination, and corpus instructions of the repository's kernels. The",
        "expected summaries are what the Python grammar of `Tools/isa/crosscheck.py` gives. -/",
        "",
        "namespace PTX.Isa.CrossCheck",
        "open PTX.Isa PTX.Syntax",
        "",
        "/-- The predicate-register oracle of the sample: canonical names. -/",
        'def isPred (n : String) : Bool := n == "%p" || n == "p"',
        "",
        "/-- Entry, slot values and operand names, types and lanes of a recognized instruction. -/",
        "def summary (r : Except String Raw) :",
        "    Option (Entry × List (Slot × Option Token) × List (String × Option Token × Nat)) :=",
        "  match r with",
        "  | .ok r => some (r.entry, r.mods, r.opnds.map fun o => (o.name, o.dtype, o.lanes))",
        "  | .error _ => none",
        "",
    ]
    for label, opcode, ops, positive in cases:
        r = run(m, opcode, ops)
        if positive and isinstance(r, Error):
            raise ValueError(f"test case {opcode} is not recognized")
        args = "[" + ", ".join(lean_operand(o) for o in ops) + "]"
        out.append(f"-- {label}")
        out.append("#guard summary (Grammar.parse isPred")
        out.append("  " + lean_opcode(opcode))
        out.append(f"  {args}) ==")
        out.append(f"  {lean_summary(m, r)}")
        out.append("")
    out.append("end PTX.Isa.CrossCheck")
    return gen_lean.fit("\n".join(out) + "\n")


# ----------------------------------------------------------------------------- Lean side

LEAN_DRIVER = r"""
import Core.Source.Isa.Grammar
open PTX.Isa PTX.Syntax

/-- Read a name up to a separator. -/
partial def readName (cs : List Char) (acc : List Char) : String × List Char :=
  match cs with
  | [] => (String.ofList acc.reverse, [])
  | c :: rest =>
    if c = ',' ∨ c = '(' ∨ c = ')' ∨ c = '\t' then (String.ofList acc.reverse, cs)
    else readName rest (c :: acc)

mutual
partial def readOp (cs : List Char) : Option (Operand × List Char) :=
  match cs with
  | 'r' :: rest => let (n, r) := readName rest []; some (.register n, r)
  | 's' :: rest => let (n, r) := readName rest []; some (.symbol n, r)
  | 'l' :: rest => let (n, r) := readName rest []; some (.literal n, r)
  | '_' :: rest => some (.sink, rest)
  | 'a' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.address os, r)
  | 'v' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.vector os, r)
  | 'p' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.pair os, r)
  | 'n' :: '(' :: rest => do
    let (o, r) ← readOp rest
    match r with
    | ')' :: r => some (.negate o, r)
    | _ => none
  | 'o' :: sg :: '(' :: rest => do
    let (b, r) ← readOp rest
    match r with
    | ',' :: r =>
      let (l, r) ← readOp r
      match r with
      | ')' :: r => some (.offset (String.singleton sg) b l, r)
      | _ => none
    | _ => none
  | _ => none
partial def readOps (cs : List Char) (acc : List Operand) : Option (List Operand × List Char) :=
  match cs with
  | ')' :: rest => some (acc.reverse, rest)
  | ',' :: rest => readOps rest acc
  | _ => do
    let (o, r) ← readOp cs
    readOps r (o :: acc)
end

def strip (p s : String) : String := if s.startsWith p then (s.drop p.length).copy else s

def tokName (t : Token) : String := strip "PTX.Isa.Token." (toString (repr t))
def slotName (s : Slot) : String := strip "PTX.Isa.Slot." (toString (repr s))
def entryName (e : Entry) : String := strip "PTX.Isa.Entry." (toString (repr e))

partial def enc : Operand → String
  | .register n => "r" ++ n
  | .symbol n => "s" ++ n
  | .literal n => "l" ++ n
  | .sink => "_"
  | .address cs => "a(" ++ ",".intercalate (cs.map enc) ++ ")"
  | .vector cs => "v(" ++ ",".intercalate (cs.map enc) ++ ")"
  | .pair cs => "p(" ++ ",".intercalate (cs.map enc) ++ ")"
  | .negate o => "n(" ++ enc o ++ ")"
  | .offset sg b l => "o" ++ sg ++ "(" ++ enc b ++ "," ++ enc l ++ ")"

def kindName : OKind → String
  | .reg => "reg" | .addr => "addr" | .ptr => "ptr" | .var => "var" | .regvar => "regvar" | .imm => "imm"
  | .label => "label"
def roleName : Role → String
  | .r => "r" | .w => "w" | .rw => "rw"

def showRaw (r : Except String Raw) : String :=
  match r with
  | .error _ => "err"
  | .ok r =>
    let mods := r.mods.map fun (s, t) => slotName s ++ "=" ++ (match t with
      | some t => tokName t | none => "-")
    let ops := r.opnds.map fun o => o.name ++ ":" ++ kindName o.kind ++ ":" ++ roleName o.role
      ++ ":" ++ (match o.dtype with | some t => tokName t | none => "-") ++ ":"
      ++ toString o.lanes ++ ":" ++ enc o.op
    " ".intercalate (["ok", entryName r.entry] ++ mods ++ ops)

def line (l : String) : String :=
  match l.splitOn "\t" with
  | [] => "bad"
  | op :: args =>
    match args.mapM (fun a => (readOp a.toList).map (·.1)) with
    | some os => showRaw (Grammar.parse (fun n => n == "%p" || n == "p") op os)
    | none => "bad"

#eval showRaw (Grammar.parse (fun _ => false) "exit" [])
"""


def lean_check(m, cases, work):
    """Run the Lean grammar on `cases` ([(opcode, operands)]); return its output lines."""
    work.mkdir(parents=True, exist_ok=True)
    inp = work / "cases.txt"
    inp.write_text("".join(op + "".join("\t" + enc(o) for o in ops) + "\n" for op, ops in cases))
    out = work / "lean_out.txt"
    driver = work / "IsaCrossCheckDriver.lean"
    driver.write_text(
        LEAN_DRIVER
        + f'\n#eval do\n  let ls := (← IO.FS.readFile "{inp}").splitOn "\\n"\n'
        + f'  IO.FS.writeFile "{out}" ("\\n".intercalate ((ls.filter (· ≠ "")).map line) ++ "\\n")\n'
    )
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env.get("PATH", "")
    if "ISA_LEAN_PATH" in env:
        env["LEAN_PATH"] = env["ISA_LEAN_PATH"]
    else:
        lp = subprocess.run(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=ROOT,
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        env["LEAN_PATH"] = lp.stdout.strip()
    res = subprocess.run(
        ["lean", "-s512000", str(driver)], cwd=ROOT, env=env, capture_output=True, text=True
    )
    if res.returncode != 0:
        raise SystemExit("lean failed:\n" + res.stdout[-3000:] + res.stderr[-3000:])
    return out.read_text().splitlines()


# ----------------------------------------------------------------------------- main


def main():
    cli = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    cli.add_argument(
        "--corpus",
        action="store_true",
        help="add the survey corpus listed by $TXVERIFY_SURVEY_INPUTS",
    )
    cli.add_argument("--no-lean", action="store_true")
    cli.add_argument("--work", type=Path, default=DEFAULT_WORK)
    cli.add_argument("--report", type=Path, help="write the per-form report as JSON")
    args = cli.parse_args()
    m = prepare(gen_lean.build_model())
    errors = []
    # corpus
    forms = {}
    for name, path in corpus_files(args.corpus).items():
        for opcode, ops in instructions(path):
            k = opcode + "".join("\t" + enc(o) for o in ops)
            f = forms.setdefault(k, {"opcode": opcode, "ops": ops, "count": 0, "files": set()})
            f["count"] += 1
            f["files"].add(name)
    cases = []
    expect = []
    for f in forms.values():
        r = run(m, f["opcode"], f["ops"])
        f["result"] = r
        cases.append((f["opcode"], f["ops"]))
        expect.append(show(m, r))
    n_corpus = len(cases)
    # synthesized
    pos, neg = synthesized(m)
    for name, combo, opcode, ops in pos:
        r = run(m, opcode, ops)
        e = m.by_name[name]
        mods = dict(zip([s[0] for s in e["slots"]], combo, strict=True))
        target = m.by_name[e.get("alias_of") or name]
        want = (target["name"], [(s[0], mods.get(s[0], "")) for s in target["slots"]])
        if isinstance(r, Error) or (r[0], r[1]) != want:
            errors.append(f"positive {name} {opcode}: {show(m, r)}")
        cases.append((opcode, ops))
        expect.append(show(m, r))
    for name, combo, opcode, ops in neg:
        r = run(m, opcode, ops)
        bad = (name, [(s[0], v) for s, v in zip(m.by_name[name]["slots"], combo, strict=True)])
        if not isinstance(r, Error) and (r[0], r[1]) == bad:
            errors.append(f"negative {name} {opcode} accepted")
        cases.append((opcode, ops))
        expect.append(show(m, r))
    errors += [f"review case {e}" for e in review_failures(m)]
    for text, _ in REVIEW_CASES:
        opcode, ops = instruction_of(text)
        cases.append((opcode, ops))
        expect.append(show(m, run(m, opcode, ops)))
    recognized = [f for f in forms.values() if not isinstance(f["result"], Error)]
    unrecognized = [f for f in forms.values() if isinstance(f["result"], Error)]
    print(
        f"corpus: {len(forms)} forms, {sum(f['count'] for f in forms.values())} instructions; "
        f"recognized {len(recognized)} forms ({sum(f['count'] for f in recognized)} "
        f"instructions), unrecognized {len(unrecognized)} forms "
        f"({sum(f['count'] for f in unrecognized)} instructions)"
    )
    print(f"synthesized: {len(pos)} positive, {len(neg)} negative")
    for path, note in PARSER_NOTES.items():
        print(f"  {path}: {note}")
    for f in sorted(unrecognized, key=lambda f: -f["count"]):
        ops = " ".join(enc(o) for o in f["ops"])
        print(f"  unrecognized x{f['count']}: {f['opcode']} {ops} ({f['result']})")
    if not args.no_lean:
        got = gen_lines = lean_check(m, cases, args.work)
        if len(gen_lines) != len(expect):
            errors.append(f"lean printed {len(got)} lines for {len(expect)} cases")
        for i, (a, b) in enumerate(zip(expect, got, strict=False)):
            if a != b:
                op, ops = cases[i]
                errors.append(f"lean/python differ on {op}: python {a!r} lean {b!r}")
        print(f"lean: {len(got)} results compared")
    if args.report:
        rep = [
            {
                "opcode": f["opcode"],
                "operands": [enc(o) for o in f["ops"]],
                "count": f["count"],
                "files": sorted(f["files"]),
                "entry": None if isinstance(f["result"], Error) else f["result"][0],
                "error": str(f["result"]) if isinstance(f["result"], Error) else None,
            }
            for f in forms.values()
        ]
        args.report.write_text(json.dumps(rep, indent=1))
    for err in errors[:50]:
        print("ERROR", err)
    if errors:
        print(f"{len(errors)} errors")
        sys.exit(1)
    print(f"crosscheck ok ({n_corpus} corpus forms)")


if __name__ == "__main__":
    main()
