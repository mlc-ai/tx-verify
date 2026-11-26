# SPDX-License-Identifier: Apache-2.0
"""Data facts and per-site `Reach` lemmas of warpgroup 0's data machine (`Proof/Wg0/Data`).

The block loop's data facts are a chain: the facts at a site are the end facts of the generated
runs after the previous site's event (`Proof/Wg0/Gen/{Mask,Peer0,Peer1,Peer2,Row}.lean`), at the
valuation `lookupD` of the previous facts with the registers the event loaded, plus the facts
still read later (`factsFrom pass (lookupD ...)`). The site table `SITES` gives, per data site of
the loop, its event pc, the runs after it and the frame stretch to the next event. Outputs:

* `Proof/Wg0/Gen/DataFacts.lean`: one def per chain link (arguments: the block's reads) and
  `wF`, the facts of a site from the block's reads;
* `Proof/Wg0/Gen/DataSites{0,1}.lean`: `reach_<pc>`, the `Reach` from after the event at `pc` to the
  next site's facts;
* `Proof/Wg0/Gen/DataSteps{0,1}.lean`: `ds_<pc>`, the data step at each site of the table (a kind of
  `Proof/Wg0/Data/Kinds.lean`); `DataSteps.lean`: `dataStep_all`.

Run with `--check` to compare with the files in the tree."""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
K = ROOT / "Kernels/FlashMlaSparseDecodeH64"
GEN = K / "Proof/Wg0/Gen"
sys.path.insert(0, str(ROOT / "Tools"))

NS = "PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data"
LO = list(range(2886, 2918))
HI = list(range(2918, 2950))
R544 = 1002
HORIZON = 1123  # the softmax-ready arrival: the block's end
RUN_FILES = (
    ["Sink", "Mask", "Peer0", "Peer1", "Peer2", "Row", "Vote", "P"]
    + [f"Rescale{c}" for c in range(4)]
    + ["EpiFacts"]
)
PLD = [(3146 + 4 * k, 3148 + 4 * k) for k in range(8)]
# The carried registers: the scale word, its pair, the running max, sum and true max.
CK = [467, 3243, 2950, 2955, 2885, 2880]


def code_table():
    import flow_gen
    import parse_ptx

    program = parse_ptx.parse((K / "v41_h64_no_split_plain.ptx").read_text())
    function = next(f for f in program.functions if not f.declaration)
    return flow_gen.flatten(function), flow_gen.register_ids(function)


def run_table():
    """name -> (n, start, end, facts0 keys, final facts name, final keys)."""
    out = {}
    for f in RUN_FILES:
        text = (GEN / f"{f}.lean").read_text()
        facts = {}
        for m in re.finditer(
            r"def (\w+) \(_?V : Nat → Value\) : List \(Nat × Value\) := \[(.*?)\n\]", text, re.S
        ):
            facts[m.group(1)] = [int(x) for x in re.findall(r"^\s*\((\d+),", m.group(2), re.M)]
        for m in re.finditer(
            r"theorem (\w+)_run .*?L g (\d+) (\d+) \((\w+) V\) (\d+)\s+\((\w+) V\)", text, re.S
        ):
            name, n, s, f0, e, fN = m.groups()
            out[name] = (int(n), int(s), int(e), facts[f0], fN, facts[fN])
    return out


CODE, IDS = code_table()
RUNS = run_table()


def writes(pcs):
    w = set()
    for pc in pcs:
        for r in CODE[pc]["writes"]:
            w.add(IDS[r])
    return w


def clos(p):
    """The local positions from `p` up to the next unguarded events (a frame set)."""
    seen, todo = set(), [p]
    while todo:
        q = todo.pop()
        c = CODE[q]
        if q in seen or (c["event"] and not c["guard"]):
            continue
        seen.add(q)
        todo += [q + 1] + ([c["target"]] if c["target"] is not None else [])
    return sorted(seen)


def read_later(k, frm):
    return any(k in [IDS.get(r) for r in CODE[pc]["reads"]] for pc in range(frm, HORIZON))


def keys_list(ks, ind=6):
    """A literal list, wrapped at 100 columns with continuation indent `ind`."""
    if not ks:
        return " []"
    lines, cur = [""], " " * ind + "["
    for i, k in enumerate(ks):
        piece = str(k) + ("]" if i == len(ks) - 1 else ",")
        if len(cur) + len(piece) + 1 > 70:
            lines.append(cur.rstrip())
            cur = " " * ind
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


# Chain links: name -> (args, keys, body). Args are (name, type) pairs.
LINKS = {}
ORDER = []


def link(name, args, keys, body):
    LINKS[name] = (args, keys, body)
    ORDER.append(name)


def call(name, args=None):
    a = args if args is not None else [x for x, _ in LINKS[name][0]]
    return f"({name} {' '.join(a)})" if a else name


def run_link(name, prev, run):
    """The link after `run` from link `prev`: the run's end facts and the facts read later."""
    args, keys, _ = LINKS[prev]
    n, s, e, k0, fN, kN = RUNS[run]
    missing = [k for k in k0 if k not in keys]
    assert not missing, (run, missing)
    w = writes(range(s, e))
    passk = [k for k in keys if k not in w and k not in kN and (k in CK or read_later(k, e))]
    assert all(k in kN + passk for k in CK if k in keys), (run, "writes a carried register")
    v = f"(lookupD {call(prev)})"
    body = f"Gen.{fN} {v} ++\n    factsFrom{keys_list(passk)}\n      {v}"
    link(name, args, kN + passk, body)
    return {"run": run, "prev": prev, "pass": passk, "k0": k0, "n": n, "s": s, "e": e}


CAR = [("x", "BitVec 64"), ("m", "Value"), ("l", "Value"), ("mx", "Value"), ("sk", "Value")]
SL = CAR + [("lo", "List Value")]
SH = CAR + [("hi", "List Value")]
SLH = CAR + [("lo", "List Value"), ("hi", "List Value")]
SM = SLH + [("mw", "Value")]


def pargs(k):
    return SM + [(f"p{j}", "Value × Value") for j in range(k)]


link("f_set", [CAR[0], CAR[4]], [467, 2880], "[(467, .bits 32 x), (2880, sk)]")
link("s_sink", [CAR[0], CAR[4], ("v", "Value")], [467, 2880, 932], "f_set x sk ++ [932].zip [v]")
link(
    "f_car",
    CAR,
    CK,
    "[(467, .bits 32 x), (3243, scPair x), (2950, m), (2955, l), (2885, mx),\n    (2880, sk)]",
)
link("f_sld1F", SH, CK + HI, "f_car x m l mx sk ++ factsFrom hiRegs (lookupD (hiRegs.zip hi))")
link("f_sld1T", SL, LO + CK, "factsFrom loRegs (lookupD (loRegs.zip lo)) ++ f_car x m l mx sk")
link(
    "f_sldw",
    SLH,
    LO + CK + HI,
    "factsFrom loRegs (lookupD (loRegs.zip lo)) ++ f_sld1F x m l mx sk hi",
)
link("s_vm", SM, LO + CK + HI + [R544], f"f_sldw x m l mx sk lo hi ++ [{R544}].zip [mw]")
STEPS = {}
STEPS["vm"] = [run_link("m_vm", "s_vm", "mask"), run_link("f_pst0", "m_vm", "pk394")]
for k in range(7):
    STEPS[f"pst{k}"] = [run_link(f"f_pst{k + 1}", f"f_pst{k}", f"pk{404 + 10 * k}")]
STEPS["bar1"] = [run_link("f_pld0", "f_pst7", "pk476")]
for k in range(8):
    a, b = PLD[k]
    pa = pargs(k + 1)
    link(
        f"s_pld{k}",
        pa,
        LINKS[f"f_pld{k}"][1] + [a, b],
        f"{call(f'f_pld{k}')} ++ [({a}, p{k}.1), ({b}, p{k}.2)]",
    )
    STEPS[f"pld{k}"] = [run_link(f"f_pld{k + 1}", f"s_pld{k}", f"sum{k}")]
STEPS["pld7"].append(run_link("f_mst", "f_pld8", "rmax"))
SP = pargs(8) + [("pm", "Value")]
link("s_mld", SP, LINKS["f_mst"][1] + [1110], f"{call('f_mst')} ++ [1110].zip [pm]")
STEPS["mld"] = [run_link("f_vote", "s_mld", "mld")]
# The vote: the branch at pc 581 skips the maximum update (pcs 582-585) when no row rescales.
KV = LINKS["f_vote"][1]
V0 = f"(lookupD {call('f_vote')})"
ONE = ".bits 32 (BitVec.ofNat 64 1065353216)"
link("f_vh", SP, KV + [2951], f"(2951, {ONE}) ::\n    factsFrom{keys_list(KV)}\n      {V0}")
ST_VT = run_link("f_vt", "f_vh", "vt")
PJ = [k for k in KV if k not in (2950, 2951) and (k in CK or read_later(k, 586))]
assert PJ == ST_VT["pass"], (PJ, ST_VT["pass"])
VH = f"(lookupD {call('f_vh')})"
link(
    "f_join",
    SP + [("vt", "Bool")],
    [2950, 2951] + PJ,
    f"let V := {VH}\n"
    "  [(2950, if vt then Gen.vt_v585 V else V 2950),\n"
    "    (2951, if vt then Gen.vt_v584 V else V 2951)] ++\n"
    f"    factsFrom{keys_list(PJ)}\n      V",
)
ST_PW = run_link("f_ost", "f_join", "pw")
# After the P stores: the facts both arms of the branch at pc 710 share (the scale factor is read
# by the dead pack at pc 712), then the rescale arm: the factor pair, and per chunk its words.
AO = LINKS["f_ost"][0]
FK = [2951] + CK
assert [k for k in LINKS["f_ost"][1] if read_later(k, 708) and k not in FK] == []
link("f_fin", AO, FK, f"factsFrom{keys_list(FK)}\n    (lookupD {call('f_ost')})")
link(
    "f_a0",
    AO,
    [3565] + FK,
    f"(3565, joinValue ((lookupD {call('f_fin')}) 2951)\n      (.bits 32 0)) ::\n    {call('f_fin')}",
)
AL = RUNS["alpha"]
assert AL[3] == [3565] and AL[5] == [3312]
BLK = [3312] + FK
link("f_blk", AO, BLK, f"Gen.{AL[4]} (lookupD {call('f_a0')}) ++\n    {call('f_fin')}")
ST_AL = {"run": "alpha", "prev": "f_a0", "H": call("f_fin"), "n": AL[0], "s": AL[1], "e": AL[2]}
ST_AL["conv"] = (
    "fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [3565]) h (by kernel_rfl),\n"
    "      h.2⟩"
)
AOO = AO + [("o", "List Value")]
ST_RS = []
for c in range(4):
    R = RUNS[f"rs{c}"]
    assert R[3] == [1199 + 129 * c + j for j in range(64)] + [3312], c
    link(
        f"f_rldw{c}",
        AOO,
        BLK + R[3][:-1],
        f"{call('f_blk')} ++\n    factsFrom (oRegs {c}) (lookupD ((oRegs {c}).zip o))",
    )
    link(
        f"f_rs{c}",
        AOO,
        R[5] + BLK,
        f"Gen.{R[4]} (lookupD {call(f'f_rldw{c}')}) ++\n    {call('f_blk')}",
    )
    ST_RS.append(
        {
            "run": f"rs{c}",
            "prev": f"f_rldw{c}",
            "H": call("f_blk"),
            "n": R[0],
            "s": R[1],
            "e": R[2],
            "k0": R[3],
        }
    )
    ST_RS[-1]["conv"] = (
        f"fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live :={keys_list(R[3])})\n"
        "      h (by kernel_rfl), ((holds_append _ _ _).mp h).1⟩"
    )


BC = "x b.m b.l b.mx b.sk"


def wf_cases():
    pw = lambda k: " ".join(f"(b.pw {j})" for j in range(k))  # noqa: E731
    lines = [
        "  | .sink => f_set x b.sk",
        f"  | .bar0 => f_car {BC}",
        f"  | .sld false 1 => f_sld1F {BC} b.hi",
        f"  | .sld true 1 => f_sld1T {BC} b.lo",
        f"  | .sldw | .tcfb | .vm => f_sldw {BC} b.lo b.hi",
    ]
    for k in range(8):
        lines.append(f"  | .pst {k} => f_pst{k} {BC} b.lo b.hi b.mw")
    lines.append(f"  | .bar1 => f_pst7 {BC} b.lo b.hi b.mw")
    for k in range(8):
        lines.append(f"  | .pld {k} => f_pld{k} {BC} b.lo b.hi b.mw {pw(k)}".rstrip())
    lines.append(f"  | .mst => f_mst {BC} b.lo b.hi b.mw {pw(8)}")
    lines.append(f"  | .vote => f_vote {BC} b.lo b.hi b.mw {pw(8)} b.pm")
    lines.append(f"  | .ost _ => f_ost {BC} b.lo b.hi b.mw {pw(8)} b.pm b.vt")
    A = f"{BC} b.lo b.hi b.mw {pw(8)} b.pm b.vt"
    lines.append(f"  | .fpx => f_fin {A}")
    lines.append(f"  | .rld _ => f_blk {A}")
    for c in range(4):
        lines.append(f"  | .rldw {c} => f_rldw{c} {A} b.o")
    for c in range(4):
        lines.append(f"  | .rst {c} => f_rs{c} {A} b.o")
    lines.append(f"  | s' => wFe (lookupD (f_car {BC})) s' b")
    return lines


SCPAIR = """/-- The scale's pair (`%rd254`, pcs 208–210): the low half of the dead pack of `%r9`, twice. -/
def scPair (x : BitVec 64) : Value :=
  joinValue (.bits (64 / 2) (truncBits (64 / 2) (x ||| (0 <<< 32))))
    (.bits (64 / 2) (truncBits (64 / 2) (x ||| (0 <<< 32))))
"""

WCLS = """
/-- The class of a site: the set-up sites share the scale, the loop head's sites the carried
statistics. -/
def wcls : Site → Site
  | .lenA | .lenB | .bwait | .arrL => .sink
  | .wv | .wq | .tcfa | .sld _ 0 => .bar0
  | .bar2 | .arrV | .mld => .mst
  | .ost _ => .ost 0
  | .rsf | .rsfb | .arrS => .fpx
  | .est | .ebar1 | .eld => .ebar0
  | .efa => .wsv
  | .ost2 c _ => .ost2 c 0
  | .old _ | .ofpx _ | .obar _ | .oel _ | .otma _ => .old 0
  | .rld _ => .rld 0
  | .rstw c => .rst c
  | s => s

/-- **The facts of a site** from the scale's bits and the block's reads. -/
def wF (x : BitVec 64) (s : Site) (b : Blk) : List (Nat × Value) := wFc x (wcls s) b"""

HEAD = """-- SPDX-License-Identifier: Apache-2.0
-- Generated by Kernels/FlashMlaSparseDecodeH64/Gen/w0site_gen.py; do not edit.
-- domain: consistent
module

{imports}
@[expose] public section

namespace {ns}
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section
"""


def facts_file():
    imps = [
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Blk",
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Sites",
    ] + [f"Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.{f}" for f in RUN_FILES]
    out = [HEAD.format(imports="".join(f"public import {i}\n" for i in imps), ns=NS)]
    out.append(SCPAIR)
    out.append("/-! The links of the chain's data facts, in chain order. -/\n")
    for name in ORDER:
        args, _, body = LINKS[name]
        groups = []
        for a, t in args:
            if groups and groups[-1][1] == t:
                groups[-1][0].append(a)
            else:
                groups.append(([a], t))
        sig = " ".join(f"({' '.join(n)} : {t})" for n, t in groups)
        head = f"def {name} {sig} : List (Nat × Value) :="
        if len(head) > 100:
            head = f"def {name} {sig} :\n    List (Nat × Value) :="
        out.append(f"{head}\n  {body}\n")
    out.append("/-- The facts of a class of sites from the block's reads. -/")
    out.append("def wFc (x : BitVec 64) : Site → Blk → List (Nat × Value)")
    out.append("  | s, b => match s with")
    out.extend("  " + ln for ln in wf_cases())
    out.append(WCLS)
    out.append("\nend\nend " + NS + "\n")
    return "\n".join(out)


def conv(prev, st):
    if "conv" in st:
        return st["conv"]
    return (
        f"fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live :={keys_list(st['k0'])})\n"
        f"      h (by kernel_rfl),\n      holds_lookupD (live :={keys_list(st['pass'])})\n"
        f"      h (by kernel_rfl)⟩"
    )


def frame(st):
    prev = st["prev"]
    v = f"(lookupD {call(prev)})"
    H = st.get("H") or f"factsFrom{keys_list(st['pass'])}\n      {v}"
    return (
        f"SegD.frame (H :={'' if not st.get('H') else chr(10) + '        '} {H}) rulesFrame\n"
        f"      (Gen.{st['run']}_run L g {v})\n      rfl (by kernel_rfl) (by kernel_rfl)\n"
        f"      fun _ _ => w0SegFree _"
    )


def reach_runs(steps):
    """A Reach through the runs `steps` to the event at the last run's end."""
    st = steps[0]
    if len(steps) == 1:
        inner = f"SegD.reach ({frame(st)})\n      Flow.code_{st['e']} trivial rfl fun _ _ h => h"
    else:
        inner = f"SegD.reach_then ({frame(st)})\n      ({reach_runs(steps[1:])})"
    return f"Reach.weaken_start ({inner})\n    ({conv(st['prev'], st)})"


def sig(args):
    groups = []
    for a, t in args:
        if groups and groups[-1][1] == t:
            groups[-1][0].append(a)
        else:
            groups.append(([a], t))
    return " ".join(f"({' '.join(n)} : {t})" for n, t in groups)


def vote_reaches():
    """The facts after the vote: the join of its two arms and the P run to the first store."""
    R = "Reach kernel Assumptions.all L g"
    args = LINKS["f_join"][0]
    a8 = " ".join(x for x, _ in LINKS["f_vote"][0])
    kv = keys_list(KV)
    out = [
        "/-- After the vote's two arms (pc 586): the P run to the first P store. -/",
        f"theorem reach_join (L : Launch) (g : Nat)\n    {sig(args)} :\n"
        f"    {R} 586\n      {call('f_join')}\n      {call('f_ost')} :=\n  {reach_runs([ST_PW])}\n",
    ]
    conv_f = (
        "fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [2950, 2951]) h\n"
        f"        (by kernel_rfl), holds_lookupD (live :={keys_list(PJ)}) h\n        (by kernel_rfl)⟩"
    )
    out.append(
        "set_option maxRecDepth 100000 in\n"
        "/-- The control code after the vote (pcs 579-580): the moved one for the factor and the\n"
        "negated vote, from any values of the carried registers. -/\n"
        f"theorem seg_vote (L : Launch) (g : Nat) (vt : Bool) (V : Nat → Value) :\n"
        f"    SegU kernel Assumptions.all L g 579 ((1, .pred vt) :: factsFrom{kv}\n      V) 581\n"
        f"      ((110, .pred (!vt)) :: (2951, {ONE}) ::\n"
        f"        factsFrom{kv}\n        V) := by\n  ctl_seg\n"
    )
    out.append("/-- After the vote (pc 578): both arms of the branch at pc 581 reach the P run. -/")
    out.append(
        f"theorem reach_578 (L : Launch) (g : Nat)\n    {sig(args)} :\n"
        f"    {R} 579\n      ((1, .pred vt) :: f_vote {a8})\n      ({call('f_ost')}) := by\n"
        f"  refine Reach.weaken_start (F := (1, .pred vt) :: factsFrom{kv}\n"
        f"      (lookupD (f_vote {a8})))\n"
        f"    (SegU.reach_then (q := 581)\n"
        f"      (G := (110, .pred (!vt)) :: f_vh {a8})\n"
        f"      (seg_vote L g vt _) ?_)\n"
        f"    (fun _ h => ⟨h.1, holds_lookupD (live :={kv}) h.2 (by kernel_rfl)⟩)\n"
        f"  cases vt\n"
        f"  · exact SegU.reach_then (SegU.branch true Flow.code_581 bra_rule (w0SegFree 581))\n"
        f"      (Reach.weaken_start\n        (reach_join L g {a8} false)\n        ({conv_f}))\n"
        f"  · exact SegU.reach_then (SegU.branch false Flow.code_581 bra_rule (w0SegFree 581))\n"
        f"      (Reach.weaken_start (SegD.reach_then ({frame(ST_VT)})\n"
        f"        (Reach.weaken_start\n          (reach_join L g {a8} true) fun _ h => h))\n"
        f"        ({conv('f_vh', ST_VT)}))\n"
    )
    return "\n".join(out)


SINK_REACH = """/-- After the sink's load (pc 156): the scaled word (pc 157) is the sink word. -/
theorem reach_156 (L : Launch) (g : Nat) (x : BitVec 64) (sk v : Value) :
    Reach kernel Assumptions.all L g 157 (s_sink x sk v) (f_set x (Gen.sk_v157 fun _ => v)) := by
  have h467 : lookupD (s_sink x sk v) 467 = .bits 32 x := by
    simp [s_sink, f_set, lookupD]
  have h932 : lookupD (s_sink x sk v) 932 = v := by
    simp [s_sink, f_set, lookupD, List.lookup]
  refine Reach.weaken_start (F := factsFrom [932] (lookupD (s_sink x sk v)) ++
      factsFrom [467] (lookupD (s_sink x sk v)))
    (SegD.reach_then (SegD.frame (H := factsFrom [467] (lookupD (s_sink x sk v))) rulesFrame
      (Gen.sk_run L g (lookupD (s_sink x sk v))) rfl (by kernel_rfl) (by kernel_rfl)
      fun _ _ => w0SegFree _)
      (reach_frameSet rulesFrame (S :=
        [158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170,
        171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 183, 184,
        185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196,
        197, 1836, 1837, 1838, 1839]) (by kernel_rfl)
        (fun _ _ => w0SegFree _) (by kernel_rfl) ?_))
    fun _ h => (holds_append _ _ _).mpr ⟨holds_lookupD (live := [932]) h (by kernel_rfl),
      holds_lookupD (live := [467]) h (by kernel_rfl)⟩
  intro R h
  have h1 := ((holds_append _ _ _).mp h).1
  have h2 := ((holds_append _ _ _).mp h).2
  have hs : Gen.sk_v157 (lookupD (s_sink x sk v)) = Gen.sk_v157 fun _ => v := by
    simp only [Gen.sk_v157, h932]
  simp only [Gen.sk_facts1, factsFrom, h467, hs, List.map_cons, List.map_nil] at h1 h2 ⊢
  exact ⟨h2.1, h1.1, trivial⟩
"""


def sites_file():
    imps = [
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts",
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.GenRules",
        "Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RulesFrame",
        "Lemmas.Flow.ReachFrame",
        "Lemmas.Flow.DataElems",
        "Tactics.KernelRfl",
    ]
    out = [HEAD.format(imports="".join(f"public import {i}\n" for i in imps), ns=NS)]
    R = "Reach kernel Assumptions.all L g"
    # Tensor Memory loads: frames only.
    H1 = "((holds_append _ _ _).mp h)"
    ZIP = f"holds_zip_lookupD {H1}.2 hl"
    tc = [  # pc, start, regs, target, S, conversion
        (
            278,
            "f_car x m l mx sk",
            "hiRegs",
            "f_sld1F x m l mx sk vals",
            [279],
            f"(holds_append _ _ _).mpr ⟨{H1}.1,\n      {ZIP}⟩",
        ),
        (
            283,
            "f_car x m l mx sk",
            "loRegs",
            "f_sld1T x m l mx sk vals",
            [284],
            f"(holds_append _ _ _).mpr ⟨{ZIP},\n      {H1}.1⟩",
        ),
        (
            280,
            "f_sld1F x m l mx sk hi",
            "loRegs",
            "f_sldw x m l mx sk vals hi",
            [281, 282],
            f"(holds_append _ _ _).mpr ⟨{ZIP},\n      {H1}.1⟩",
        ),
        (
            285,
            "f_sld1T x m l mx sk lo",
            "hiRegs",
            "f_sldw x m l mx sk lo vals",
            [],
            f"(holds_append _ _ _).mpr ⟨((holds_append _ _ _).mp {H1}.1).1,\n"
            f"      (holds_append _ _ _).mpr\n        ⟨((holds_append _ _ _).mp {H1}.1).2,\n          {ZIP}⟩⟩",
        ),
    ]
    for pc, start, regs, tgt, S, cv in tc:
        args = CAR + {278: [], 283: [], 280: SH[5:], 285: SL[5:]}[pc]
        out.append(f"/-- After the score load at pc {pc}. -/")
        out.append(
            f"theorem reach_{pc} (L : Launch) (g : Nat) {sig(args)} (vals : List Value)\n"
            f"    (hl : vals.length = {regs}.length) :\n"
            f"    {R} {pc + 1} ({start} ++ {regs}.zip vals) ({tgt}) :=\n"
            f"  reach_frameSet rulesFrame (S := [{', '.join(map(str, S))}]) (by kernel_rfl)\n"
            f"    (fun _ _ => w0SegFree _) (by kernel_rfl) fun _ h =>\n    {cv}\n"
        )
    out.append(SINK_REACH)
    kept = [(pc, "f_set") for pc in (168, 181, 198)]
    kept += [(pc, "f_car") for pc in (256, 264, 272, 275)]
    kept += [(286, "f_sldw"), (287, "f_sldw"), (473, "f_pst7")]
    kept += [(566, "f_mst"), (569, "f_mst"), (571, "f_mst")]
    kept += [(704 + k, "f_ost") for k in range(3)]
    for pc, F in kept:
        ty = sig(LINKS[F][0])
        a = " ".join(x for x, _ in LINKS[F][0])
        S = {286: [], 287: [288], 473: [474]}.get(pc, clos(pc + 1))
        out.append(f"/-- After the event at pc {pc}: the facts kept. -/")
        out.append(
            f"theorem reach_{pc} (L : Launch) (g : Nat) {ty} :\n"
            f"    {R} {pc + 1} ({F} {a}) ({F} {a}) :=\n"
            f"  reach_frameSet rulesFrame (S :={keys_list(S)}) (by kernel_rfl)\n"
            f"    (fun _ _ => w0SegFree _) (by kernel_rfl) fun _ h => h\n"
        )
    sites = [("vm", 289, "s_vm", "f_pst0")]
    for k in range(7):
        sites.append((f"pst{k}", 403 + 10 * k, f"f_pst{k}", f"f_pst{k + 1}"))
    sites.append(("bar1", 475, "f_pst7", "f_pld0"))
    for k in range(7):
        sites.append((f"pld{k}", 477 + 5 * k, f"s_pld{k}", f"f_pld{k + 1}"))
    sites += [("pld7", 512, "s_pld7", "f_mst"), ("mld", 572, "s_mld", "f_vote")]
    split = None
    for key, pc, start, tgt in sites:
        if key == "pld0":
            out.append("end\nend " + NS + "\n")
            split = len(out)
            out.append(
                HEAD.format(
                    imports="".join(
                        f"public import {i}\n"
                        for i in [
                            "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites0",
                            "Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps",
                            "Lemmas.Flow.ReachSegU",
                            "Lemmas.Flow.BranchU",
                        ]
                    ),
                    ns=NS,
                )
            )
        args = LINKS[start][0]
        a = [x for x, _ in args]
        out.append(f"/-- After the event at pc {pc}. -/")
        out.append(
            f"theorem reach_{pc} (L : Launch) (g : Nat)\n    {sig(args)} :\n"
            f"    {R} {pc + 1}\n      {call(start)}\n      {call(tgt, a)} :=\n"
            f"  {reach_runs(STEPS[key])}\n"
        )
    out.append(vote_reaches())
    out.append("end\nend " + NS + "\n")
    return "\n".join(out[:split]), "\n".join(out[split:])


def sites2_file():
    """The reaches of the rescale arm: from the P stores to the softmax-ready arrival."""
    imps = [
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites1",
        "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.DeadPack",
    ]
    out = [HEAD.format(imports="".join(f"public import {i}\n" for i in imps), ns=NS)]
    R = "Reach kernel Assumptions.all L g"
    sg = sig(AO)
    a = " ".join(x for x, _ in AO)
    a + " o"
    sgo = sg + " (o : List Value)"
    FKL = keys_list(FK)
    FR = "reach_frameSet rulesFrame (S :={S}) (by kernel_rfl)\n    (fun _ _ => w0SegFree _) (by kernel_rfl) fun _ h =>\n    {cv}\n"
    out.append(
        "/-- After the last P store (pc 707): both arms of the branch at pc 710 keep the facts. -/"
    )
    out.append(
        f"theorem reach_707 (L : Launch) (g : Nat) {sg} :\n    {R} 708 ({call('f_ost')}) "
        f"({call('f_fin')}) :=\n  "
        + FR.format(S=keys_list(clos(708)), cv=f"holds_lookupD (live :={FKL}) h (by kernel_rfl)")
    )
    out.append(
        "/-- After the rescale fence (pc 711): the factor pair, to the first chunk's load. -/"
    )
    out.append(
        f"theorem reach_711 (L : Launch) (g : Nat) {sg} :\n    {R} 712 ({call('f_fin')})\n"
        f"      ({call('f_blk')}) :=\n"
        f"  SegU.reach_then (q := 713) (G :=\n      {call('f_a0')})\n"
        f"    (seg_712 L g (lookupD {call('f_ost')}))\n"
        f"    ({reach_runs([ST_AL])})\n"
    )
    for c in range(4):
        pc = 716 + 101 * c
        H1 = "((holds_append _ _ _).mp h)"
        out.append(f"/-- After the chunk {c}'s load (pc {pc}). -/")
        out.append(
            f"theorem reach_{pc} (L : Launch) (g : Nat) {sg} (vals : List Value)\n"
            f"    (hl : vals.length = (oRegs {c}).length) :\n"
            f"    {R} {pc + 1} ({call('f_blk')} ++ (oRegs {c}).zip vals)\n"
            f"      ({call(f'f_rldw{c}', a.split() + ['vals'])}) :=\n  "
            + FR.format(
                S=" []",
                cv=f"(holds_append _ _ _).mpr ⟨{H1}.1,\n      holds_zip_lookupD {H1}.2 hl⟩",
            )
        )
        out.append(f"/-- After the chunk {c}'s load wait (pc {pc + 1}): the rescaled words. -/")
        out.append(
            f"theorem reach_{pc + 1} (L : Launch) (g : Nat) {sgo} :\n"
            f"    {R} {pc + 2}\n      ({call(f'f_rldw{c}')})\n      ({call(f'f_rs{c}')}) :=\n"
            f"  {reach_runs([ST_RS[c]])}\n"
        )
        pst = [814, 915, 1016, 1117][c]
        out.append(f"/-- After the chunk {c}'s store (pc {pst}): the facts are kept. -/")
        out.append(
            f"theorem reach_{pst} (L : Launch) (g : Nat) {sgo} :\n"
            f"    {R} {pst + 1} ({call(f'f_rs{c}')})\n      ({call(f'f_rs{c}')}) :=\n  "
            + FR.format(S=" []", cv="h")
        )
        out.append(
            f"/-- After the chunk {c}'s store wait (pc {pst + 1}): the next chunk's start. -/"
        )
        if c < 3:
            tgt, S, cv = call("f_blk"), clos(pst + 2), "((holds_append _ _ _).mp h).2"
        else:
            tgt, S = call("f_fin"), []
            cv = "((holds_append _ _ _).mp ((holds_append _ _ _).mp h).2).2"
        out.append(
            f"theorem reach_{pst + 1} (L : Launch) (g : Nat) {sgo} :\n"
            f"    {R} {pst + 2} ({call(f'f_rs{c}')})\n      ({tgt}) :=\n  "
            + FR.format(S=keys_list(S), cv=cv)
        )
    out.append("/-- After the closing fence (pc 1119). -/")
    out.append(
        f"theorem reach_1119 (L : Launch) (g : Nat) {sg} :\n"
        f"    {R} 1120 ({call('f_fin')})\n      ({call('f_fin')}) :=\n  "
        + FR.format(S=" []", cv="h")
    )
    out.append("/-- After the proxy fence (pc 1120). -/")
    out.append(
        f"theorem reach_1120 (L : Launch) (g : Nat) {sg} :\n"
        f"    {R} 1121 ({call('f_fin')})\n      ({call('f_fin')}) :=\n  "
        + FR.format(S=keys_list(clos(1121)), cv="h")
    )
    MV = "\n        ".join(f"(lookupD ({call('f_fin')}) {k})" for k in CK[2:])
    out.append("/-- After the softmax-ready arrival (pc 1122): the next block's head's facts. -/")
    out.append(
        f"theorem reach_1122 (L : Launch) (g : Nat) {sg} :\n"
        f"    {R} 1123 ({call('f_fin')})\n"
        f"      (f_car x\n        {MV}) :=\n  "
        + FR.format(
            S=keys_list(clos(1123)),
            cv=f"by\n      have h' := holds_lookupD (live :={keys_list(CK)}) h\n"
            "        (by kernel_rfl)\n      exact h'",
        )
    )
    out.append("end\nend " + NS + "\n")
    return "\n".join(out)


DS_HEAD = """-- SPDX-License-Identifier: Apache-2.0
-- Generated by Kernels/FlashMlaSparseDecodeH64/Gen/w0site_gen.py; do not edit.
-- domain: consistent
module

{imports}
@[expose] public section

namespace {ns}
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {{P : Params}} {{L : Launch}} {{g : Nat}} {{w : BitVec 64}} {{m0 : Mem0}}
"""

DS_IMPORTS0 = """public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Kinds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSites2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Setup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Arr
"""
DS_IMPORTS1 = """public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataSteps0
"""
DS_IMPORTS2 = """public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.EpiSites
"""

INTRO = "  rintro ⟨⟨_, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, hist, ok⟩ ⟨⟩\n"
SUCC = "(fun c' h => congrArg wcls (by simpa [succOk] using h))"
MSUCC = "(fun c' h => cls_mem h (by decide))"
CA = "(scX L) b.m b.l b.mx b.sk"
NOST = "(by intro h; cases h)"
BM = "b.lo b.hi b.mw " + " ".join(f"(b.pw {j})" for j in range(8))
PWS = " ".join(f"(b.pw {j})" for j in range(8))
BV = f"b.lo b.hi b.mw\n      {PWS} b.pm b.vt"


def ds_lemma(pc, site, body):
    return (
        f"theorem ds_{pc} : ∀ d : D, d.c.site = {site} →\n"
        f"    DataStep (code P L g w) (dF L) d := by\n{INTRO}  exact {body}\n"
    )


def steps_file():
    out = [DS_HEAD.format(ns=NS, imports=DS_IMPORTS0)]
    tc = [
        (278, ".sld false 0", ".sld false 1", NOST, f"reach_278 L g {CA} vals hl"),
        (283, ".sld true 0", ".sld true 1", NOST, f"reach_283 L g {CA} vals hl"),
        (280, ".sld false 1", ".sldw", NOST, f"reach_280 L g {CA} b.hi vals hl"),
        (285, ".sld true 1", ".sldw", NOST, f"reach_285 L g {CA} b.lo vals hl"),
    ]
    for pc, s, s2, st, r in tc:
        out.append(f"/-- The score load at pc {pc}. -/")
        out.append(
            ds_lemma(
                pc,
                f"({s})",
                f"@ds_tc P L g w _ ({s}) ({s2}) _ _ rfl (by decide)\n"
                f"    Flow.code_{pc} rfl {SUCC} {st}\n    (by decide) (hoff_of (by kernel_rfl))\n"
                f"    fun _ vals hl => {r}",
            )
        )
    out.append("/-- The `.nc` load at pc 156 (the sink word). -/")
    out.append(
        ds_lemma(
            156,
            "(.sink)",
            f"@ds_ncv P L g w _ (.sink) (.sink) _ _ _ _ _ rfl (by decide) Flow.code_156\n"
            f"    rfl rfl rfl rfl rfl rfl rfl rfl\n    {MSUCC} {NOST}\n"
            f"    (hne_of (by kernel_rfl)) fun _ bs => reach_156 L g (scX L) b.sk (loadVal bs)",
        )
    )
    for pc, s, s2 in [(168, ".lenA", ".sink"), (181, ".lenB", ".bwait")]:
        out.append(f"/-- The `.nc` load at pc {pc}. -/")
        out.append(
            ds_lemma(
                pc,
                f"({s})",
                f"@ds_nc P L g w _ ({s}) ({s2}) _ _ _ _ _ rfl (by decide) Flow.code_{pc}\n"
                f"    rfl rfl rfl rfl rfl rfl rfl rfl\n"
                f"    {MSUCC if s2 == '.sink' else SUCC} {NOST}\n"
                f"    (hne_of (by kernel_rfl)) fun _ => reach_{pc} L g (scX L) b.sk",
            )
        )
    for pc, s in [(264, ".wv"), (272, ".wq")]:
        out.append(f"/-- The poll at pc {pc}. -/")
        out.append(
            ds_lemma(
                pc,
                f"({s})",
                f"@ds_wait P L g w _ ({s}) (.bar0) _ _ _ _ _ _ rfl (by decide) Flow.code_{pc} rfl\n"
                f"    {MSUCC} {NOST}\n"
                f"    (hne_of (by kernel_rfl)) fun _ => reach_{pc} L g {CA}",
            )
        )
    nx = [
        (198, ".bwait", ".arrL", "Control.fires_bulkWait_next", "reach_198 L g (scX L) b.sk"),
        (256, ".bar0", ".wv", "fires_barSyncN_next", f"reach_256 L g {CA}"),
        (275, ".tcfa", ".bar0", "Code.fires_tcPlain_next (.inl rfl)", f"reach_275 L g {CA}"),
        (286, ".sldw", ".tcfb", "fires_tcWaitLd_next", f"reach_286 L g {CA} b.lo b.hi"),
        (287, ".tcfb", ".vm", "fires_tcFenceBefore_next", f"reach_287 L g {CA} b.lo b.hi"),
        (475, ".bar1", ".pld 0", "fires_barSyncN_next", f"reach_475 L g {CA} b.lo b.hi b.mw"),
        (569, ".bar2", ".arrV", "fires_barSyncN_next", f"reach_569 L g {CA} {BM}"),
        (571, ".arrV", ".mld", "Code.fires_arrive_next", f"reach_571 L g {CA} {BM}"),
    ]
    for pc, s, s2, fu, r in nx:
        out.append(f"/-- The event at pc {pc}. -/")
        out.append(
            ds_lemma(
                pc,
                f"({s})",
                f"@ds_nx P L g w _ ({s}) ({s2}) _ rfl (by decide)\n"
                f"    Flow.code_{pc} (fun _ _ _ hf => {fu} hf) rfl\n"
                f"    {MSUCC if pc == 275 else SUCC} {NOST}\n"
                f"    fun _ => {r}",
            )
        )
    out.append("/-- The valid-mask load (pc 289). -/")
    out.append(
        ds_lemma(
            289,
            "(.vm)",
            f"@ds_ld1 P L g w _ (.vm) (.pst 0) _ _ rfl (by decide)\n"
            f"    Flow.code_289 rfl rfl rfl rfl rfl rfl\n    {SUCC} {NOST}\n"
            f"    (hoff_of (by kernel_rfl)) fun _ bs => reach_289 L g {CA} b.lo b.hi (loadVal bs)",
        )
    )
    for k in range(8):
        pc = 403 + 10 * k
        s2 = f".pst {k + 1}" if k < 7 else ".bar1"
        out.append(f"/-- The packed peer store {k} (pc {pc}). -/")
        out.append(
            ds_lemma(
                pc,
                f"(.pst {k})",
                f"@ds_st P L g w _ (.pst {k}) ({s2}) _ rfl (by decide)\n"
                f"    Flow.code_{pc} rfl rfl rfl {SUCC} {NOST}\n"
                f"    fun _ => reach_{pc} L g {CA} b.lo b.hi b.mw",
            )
        )
    out.append("end\nend " + NS + "\n")
    split1 = len(out)
    out.append(DS_HEAD.format(ns=NS, imports=DS_IMPORTS1))
    for k in range(8):
        pc = 477 + 5 * k
        s2 = f".pld {k + 1}" if k < 7 else ".mst"
        ps = " ".join(f"(b.pw {j})" for j in range(k))
        r = f"reach_{pc} L g {CA} b.lo b.hi b.mw {ps}".rstrip() + "\n      (a0, loadVal bs)"
        r = r.replace("  (", " (")
        out.append(f"/-- The peer load {k} (pc {pc}). -/")
        out.append(
            ds_lemma(
                pc,
                f"(.pld {k})",
                f"@ds_ld2 P L g w _ {k} ({s2}) _ _ _ rfl\n"
                f"    Flow.code_{pc} rfl rfl rfl rfl rfl (by decide)\n"
                f"    (fun c' hel h => congrArg wcls (by simpa [succOk, hel] using h))\n"
                f"    (hoff_of (by kernel_rfl))\n"
                f"    fun bs _ => {r}",
            )
        )
    out.append("/-- The row maximum's store (pc 566). -/")
    out.append(
        ds_lemma(
            566,
            "(.mst)",
            f"@ds_st P L g w _ (.mst) (.bar2) _ rfl (by decide)\n"
            f"    Flow.code_566 rfl rfl rfl {SUCC} {NOST}\n"
            f"    fun _ => reach_566 L g {CA} {BM}",
        )
    )
    out.append("/-- The partner's row maximum (pc 572). -/")
    out.append(
        ds_lemma(
            572,
            "(.mld)",
            f"@ds_ld1 P L g w _ (.mld) (.vote) _ _ rfl (by decide)\n"
            f"    Flow.code_572 rfl rfl rfl rfl rfl rfl\n    {SUCC} {NOST}\n"
            f"    (hoff_of (by kernel_rfl)) fun _ bs => reach_572 L g {CA} {BM} (loadVal bs)",
        )
    )
    out.append("/-- The rescale vote (pc 578). -/")
    out.append(
        ds_lemma(
            578,
            "(.vote)",
            f"@ds_vote P L g w _ (.vote) (.ost 0) _ _ _ _ _ rfl (by decide)\n"
            f"    Flow.code_578 rfl {SUCC} {NOST} (hne_of (by kernel_rfl))\n"
            f"    fun _ _ r => reach_578 L g {CA} {BM} b.pm r",
        )
    )
    for k in range(4):
        pc = 704 + k
        s2 = f".ost {k + 1}" if k < 3 else ".fpx"
        hs = "(fun c' hel h => congrArg wcls (by simpa [succOk, hel] using h))"
        if k == 3:
            hs = (
                "(fun c' hel h => by\n"
                "      rcases (by simpa [succOk, hel] using h : c'.site = .rsf ∨ c'.site = .fpx)\n"
                "        with h' | h' <;> simp [h', wcls])"
            )
        hr = f"fun _ _ _ _ => reach_{pc} L g {CA}\n      {BV}"
        out.append(f"/-- The P store {k} (pc {pc}). -/")
        out.append(
            ds_lemma(
                pc,
                f"(.ost {k})",
                f"@ds_stE P L g w _ (.ost {k}) ({s2}) _ 4 rfl (by decide)\n"
                f"    Flow.code_{pc} rfl rfl rfl (by simp [Control.D.acc])\n"
                f"    (fun c' hel h => congrArg wcls (by simpa [succOk, hel] using h))\n"
                f"    (fun _ => rfl) rfl\n    {hs}\n    ({hr})",
            )
        )
    BO = BV + " b.o"
    out.append("/-- The rescale fence (pc 711). -/")
    out.append(
        ds_lemma(
            711,
            "(.rsf)",
            f"@ds_nx P L g w _ (.rsf) (.rld 0) _ rfl (by decide)\n"
            f"    Flow.code_711 (fun _ _ _ hf => Code.fires_tcPlain_next (.inl rfl) hf) rfl\n"
            f"    {SUCC} {NOST}\n    fun _ => reach_711 L g {CA}\n      {BV}",
        )
    )
    for c in range(4):
        pl = 716 + 101 * c
        pst = [814, 915, 1016, 1117][c]
        nxt = f".rld {c + 1}" if c < 3 else ".rsfb"
        out.append(f"/-- The load of rescale chunk {c} (pc {pl}). -/")
        out.append(
            ds_lemma(
                pl,
                f"(.rld {c})",
                f"@ds_tc P L g w _ (.rld {c}) (.rldw {c}) _ _ rfl (by decide)\n"
                f"    Flow.code_{pl} rfl {SUCC} {NOST}\n    (by decide) (hoff_of (by kernel_rfl))\n"
                f"    fun _ vals hl => reach_{pl} L g {CA}\n      {BV} vals hl",
            )
        )
        out.append(f"/-- The wait for rescale chunk {c}'s load (pc {pl + 1}). -/")
        out.append(
            ds_lemma(
                pl + 1,
                f"(.rldw {c})",
                f"@ds_nx P L g w _ (.rldw {c}) (.rst {c}) _ rfl (by decide)\n"
                f"    Flow.code_{pl + 1} (fun _ _ _ hf => fires_tcWaitLd_next hf) rfl\n"
                f"    {SUCC} {NOST}\n    fun _ => reach_{pl + 1} L g {CA}\n      {BO}",
            )
        )
        out.append(f"/-- The store of rescale chunk {c} (pc {pst}). -/")
        out.append(
            ds_lemma(
                pst,
                f"(.rst {c})",
                f"@ds_tcSt P L g w _ (.rst {c}) (.rstw {c}) _ _ _ rfl (by decide)\n"
                f"    Flow.code_{pst} (by decide +kernel) rfl\n"
                f"    {SUCC} {NOST}\n    fun _ => reach_{pst} L g {CA}\n      {BO}",
            )
        )
        out.append(f"/-- The wait for rescale chunk {c}'s store (pc {pst + 1}). -/")
        out.append(
            ds_lemma(
                pst + 1,
                f"(.rstw {c})",
                f"@ds_nx P L g w _ (.rstw {c}) ({nxt}) _ rfl (by decide)\n"
                f"    Flow.code_{pst + 1} (fun _ _ _ hf => fires_tcWaitSt_next hf) rfl\n"
                f"    {SUCC} {NOST}\n    fun _ => reach_{pst + 1} L g {CA}\n      {BO}",
            )
        )
    out.append("/-- The closing fence of the rescale arm (pc 1119). -/")
    out.append(
        ds_lemma(
            1119,
            "(.rsfb)",
            f"@ds_nx P L g w _ (.rsfb) (.fpx) _ rfl (by decide)\n"
            f"    Flow.code_1119 (fun _ _ _ hf => Code.fires_tcPlain_next (.inr (.inl rfl)) hf) rfl\n"
            f"    {SUCC} {NOST}\n    fun _ => reach_1119 L g {CA}\n      {BV}",
        )
    )
    out.append("/-- The proxy fence before the softmax-ready arrival (pc 1120). -/")
    out.append(
        ds_lemma(
            1120,
            "(.fpx)",
            f"@ds_nx P L g w _ (.fpx) (.arrS) _ rfl (by decide)\n"
            f"    Flow.code_1120 (fun _ _ _ hf => Option.some.inj (fires_fence_proxy hf).2) rfl\n"
            f"    {SUCC} {NOST}\n    fun _ => reach_1120 L g {CA}\n      {BV}",
        )
    )
    out.append("end\nend " + NS + "\n")
    split2 = len(out)
    out.append(DS_HEAD.format(ns=NS, imports=DS_IMPORTS2))
    out.append(DS_ALL)
    out.append("end\nend " + NS + "\n")
    return ["\n".join(out[:split1]), "\n".join(out[split1:split2]), "\n".join(out[split2:])]


DS_ALL = """/-- **The data step of every state.** -/
theorem dataStep_all (hp : Pre P L m0) (d : D) : DataStep (code P L g w) (dF L) d := by
  cases hc : onChain d.c.site
  · exact ds_off (fun h => by simp [onChain, h] at hc) fun _ => succOk_off hc
  obtain ⟨⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩, b, hist, ok⟩ := d
  cases s <;> simp only [onChain, Bool.false_eq_true] at hc
  · exact ds_103 hp _ rfl
  · exact ds_156 _ rfl
  · exact ds_168 _ rfl
  · exact ds_181 _ rfl
  · exact ds_198 _ rfl
  · exact ds_200 _ rfl
  · exact ds_256 _ rfl
  · exact ds_264 _ rfl
  · exact ds_272 _ rfl
  · exact ds_275 _ rfl
  · rename_i a k
    fin_cases k <;> cases a
    · exact ds_278 _ rfl
    · exact ds_283 _ rfl
    · exact ds_280 _ rfl
    · exact ds_285 _ rfl
  · exact ds_286 _ rfl
  · exact ds_287 _ rfl
  · exact ds_289 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_403 _ rfl
    · exact ds_413 _ rfl
    · exact ds_423 _ rfl
    · exact ds_433 _ rfl
    · exact ds_443 _ rfl
    · exact ds_453 _ rfl
    · exact ds_463 _ rfl
    · exact ds_473 _ rfl
  · exact ds_475 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_477 _ rfl
    · exact ds_482 _ rfl
    · exact ds_487 _ rfl
    · exact ds_492 _ rfl
    · exact ds_497 _ rfl
    · exact ds_502 _ rfl
    · exact ds_507 _ rfl
    · exact ds_512 _ rfl
  · exact ds_566 _ rfl
  · exact ds_569 _ rfl
  · exact ds_571 _ rfl
  · exact ds_572 _ rfl
  · exact ds_578 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_704 _ rfl
    · exact ds_705 _ rfl
    · exact ds_706 _ rfl
    · exact ds_707 _ rfl
  · exact ds_711 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_716 _ rfl
    · exact ds_817 _ rfl
    · exact ds_918 _ rfl
    · exact ds_1019 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_717 _ rfl
    · exact ds_818 _ rfl
    · exact ds_919 _ rfl
    · exact ds_1020 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_814 _ rfl
    · exact ds_915 _ rfl
    · exact ds_1016 _ rfl
    · exact ds_1117 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_815 _ rfl
    · exact ds_916 _ rfl
    · exact ds_1017 _ rfl
    · exact ds_1118 _ rfl
  · exact ds_1119 _ rfl
  · exact ds_1120 _ rfl
  · exact ds_1122 _ rfl
  · exact ds_1154 _ rfl
  · exact ds_1155 _ rfl
  · exact ds_1156 _ rfl
  · exact ds_1157 hp rfl
  · exact ds_1178 _ rfl
  · exact ds_1184 _ rfl
  · exact ds_1187 hp rfl
  · rename_i k
    fin_cases k
    · exact ds_1201 _ rfl
    · exact ds_1361 _ rfl
    · exact ds_1519 _ rfl
    · exact ds_1676 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_1202 _ rfl
    · exact ds_1362 _ rfl
    · exact ds_1520 _ rfl
    · exact ds_1677 _ rfl
  · rename_i c k
    fin_cases c <;> fin_cases k
    · exact ds_1331 _ rfl
    · exact ds_1332 _ rfl
    · exact ds_1333 _ rfl
    · exact ds_1334 _ rfl
    · exact ds_1335 _ rfl
    · exact ds_1336 _ rfl
    · exact ds_1337 _ rfl
    · exact ds_1338 _ rfl
    · exact ds_1491 _ rfl
    · exact ds_1492 _ rfl
    · exact ds_1493 _ rfl
    · exact ds_1494 _ rfl
    · exact ds_1495 _ rfl
    · exact ds_1496 _ rfl
    · exact ds_1497 _ rfl
    · exact ds_1498 _ rfl
    · exact ds_1649 _ rfl
    · exact ds_1650 _ rfl
    · exact ds_1651 _ rfl
    · exact ds_1652 _ rfl
    · exact ds_1653 _ rfl
    · exact ds_1654 _ rfl
    · exact ds_1655 _ rfl
    · exact ds_1656 _ rfl
    · exact ds_1806 _ rfl
    · exact ds_1807 _ rfl
    · exact ds_1808 _ rfl
    · exact ds_1809 _ rfl
    · exact ds_1810 _ rfl
    · exact ds_1811 _ rfl
    · exact ds_1812 _ rfl
    · exact ds_1813 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_1339 _ rfl
    · exact ds_1499 _ rfl
    · exact ds_1657 _ rfl
    · exact ds_1814 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_1342 _ rfl
    · exact ds_1502 _ rfl
    · exact ds_1659 _ rfl
    · exact ds_1817 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_1350 _ rfl
    · exact ds_1507 _ rfl
    · exact ds_1664 _ rfl
    · exact ds_1822 _ rfl
  · rename_i k
    fin_cases k
    · exact ds_1358 _ rfl
    · exact ds_1516 _ rfl
    · exact ds_1673 _ rfl
    · exact ds_1831 _ rfl

/-- **A data state obeys its obligations** from the control machine's (`Over.stepAtU`). -/
theorem stepAtU (hp : Pre P L m0) (hS : ∀ c, (Control.code P L g w).StepAtU c) (d : D) :
    (code P L g w).StepAtU d :=
  (over P L g w).stepAtU hS (dataStep_all hp d)
"""


def wrap_line(line):
    """Break a line over 100 columns at spaces outside brackets (continuation indent +4)."""
    if len(line) <= 100:
        return [line]
    ind = " " * (len(line) - len(line.lstrip()) + 4)
    pieces, cur, depth = [], "", 0
    for ch in line:
        depth += (ch in "([{⟨") - (ch in ")]}⟩")
        if ch == " " and depth == 0 and cur.strip():
            pieces.append(cur)
            cur = ""
        cur += ch
    pieces.append(cur)
    out, acc = [], pieces[0]
    for pc in pieces[1:]:
        if len(acc) + len(pc) > 100:
            out.append(acc)
            acc = ind + pc.lstrip()
        else:
            acc += pc
    out.append(acc)
    return out


def wrap(text):
    return "\n".join(x for ln in text.split("\n") for x in wrap_line(ln))


def main():
    sites0, sites1 = sites_file()
    outs = {
        GEN / "DataFacts.lean": wrap(facts_file()),
        GEN / "DataSites0.lean": wrap(sites0),
        GEN / "DataSites1.lean": wrap(sites1),
        GEN / "DataSites2.lean": wrap(sites2_file()),
    }
    for name, text in zip(["DataSteps0", "DataSteps1", "DataSteps"], steps_file()):
        outs[GEN / f"{name}.lean"] = wrap(text)
    check = "--check" in sys.argv
    for path, text in outs.items():
        if check:
            if not path.exists() or path.read_text() != text:
                sys.exit(f"w0site_gen: {path.relative_to(ROOT)} is stale")
        else:
            path.write_text(text)


if __name__ == "__main__":
    main()
