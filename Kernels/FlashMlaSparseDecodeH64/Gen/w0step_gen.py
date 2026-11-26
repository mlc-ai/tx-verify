#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Strict steps (`Code.StepFor`) of warpgroup 0's data machine at the data-only windows.

For the sites `DATA_ONLY` of the tolerant `ds_<pc>` (`Proof/Wg0/Gen/DataSteps*.lean`) writes `sk_<pc>`:
the strict step of the state at the site, from the kind lemma (`Data/StepKinds.lean`) and the exact
window segment `segS_<pc>` (`Gen/w0seg_gen.py`), under the window's conditions (hypotheses).
Output: `Proof/Wg0/Gen/StepS<n>.lean`.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
GEN = ROOT / "Kernels/FlashMlaSparseDecodeH64/Proof/Wg0/Gen"
NS = "Kernels.FlashMlaSparseDecodeH64.Proof.Wg0"
SEGS = ["SegS0", "SegS1", "SegS2", "SegS3", "SegS4", "SegS5", "SegS6"]
OUT = {  # output file -> (pcs, imports)
    "StepS0": [475, 717, 818, 919, 1020, 1202, 1362, 1520, 1677] + [403 + 10 * k for k in range(7)],
    "StepS1": [289, 572] + [477 + 5 * k for k in range(8)],
}
LD1_REG = {289: 1002, 572: 1110}
LD1_FIELD = {289: "mw", 572: "pm"}
ERASE = {572: 1112}  # the window writes this control register (the successor's control fact)


def blocks(files):
    out = {}
    for f in files:
        text = (GEN / f"{f}.lean").read_text()
        for b in re.split(r"\n(?=/-- |theorem |def )", text):
            m = re.search(r"theorem (?:ds|segS)_(\d+) ", b)
            if m:
                out[(f, m.group(0).split("_")[0].split()[-1], int(m.group(1)))] = b
    return out


def top_tokens(s):
    toks, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(⟨[":
            depth += 1
        elif ch in ")⟩]":
            depth -= 1
        if ch in " \n" and depth == 0:
            if cur:
                toks.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        toks.append(cur)
    return toks


def parse_seg(b):
    m = re.search(r"theorem segS_(\d+) \(L : Launch\) \(g : Nat\)\s*(.*?)\s*\(Hc Hc'", b, re.S)
    pc, binders = int(m.group(1)), m.group(2)
    names = []
    for grp in re.findall(r"\(([^():]*) :", binders):
        names += grp.split()
    end = int(re.search(r"ctlLive (\d+)\)", b).group(1))
    start = int(re.search(r"Seg kernel Assumptions\.all L g n (\d+)", b).group(1))
    conds = re.findall(r"\(c\d+ : (Gen\.\w+_cond \(lookupD \(.*?\)\))\)", b, re.S)
    conds = [re.sub(r"\s+", " ", c) for c in conds]
    fm = re.search(r"\(Hc \+\+ (.*?)\)\s+(\d+)\s*\n\s*\(Hc' \+\+", b, re.S)
    F = re.sub(r"\s+", " ", fm.group(1))
    return dict(pc=pc, names=names, end=end, start=start, conds=conds, F=F)


def subst(text, names, args):
    mp = dict(zip(names, args))
    return re.sub(r"\b[A-Za-z_]\w*\b", lambda m: mp.get(m.group(0), m.group(0)), text)


def gen(pc, ds, seg):
    kind = re.search(r"@ds_(\w+) P L g w", ds).group(1)
    site = re.search(r"d\.c\.site = \((.*?)\) →", ds).group(1)
    m = re.search(rf"reach_{pc} L g (.*?)\s*\n\s*\n|reach_{pc} L g (.*)$", ds, re.S)
    argtxt = (m.group(1) or m.group(2)).strip()
    args = top_tokens(argtxt)
    assert len(args) == len(seg["names"]), (pc, args, seg["names"])
    args = [a if a.startswith("(") else a for a in args]
    pargs = [a if (a.startswith("(") or "." not in a or True) else a for a in args]
    args = [re.sub(r"\bb\.", "d.b.", a) for a in args]
    pargs = [a if a.startswith("(") else f"({a})" for a in args]
    conds = [subst(c, seg["names"], pargs) for c in seg["conds"]]
    F = subst(seg["F"], seg["names"], pargs)
    nxt = re.search(r"@ds_\w+ P L g w _ (?:\d+|\(.*?\)) \((.*?)\) _", ds).group(1)
    reset = site.split()[0] in (".bar1", ".oldw")
    cnew = "{ d.c with site := " + nxt + (", el := 0 }" if reset else " }")
    if kind == "ld2":
        cnew = "{ d.c with site := " + nxt + ", el := 0, a0 := .pred false }"
    hyps = "".join(f"\n    (c{i + 1} : {c})" for i, c in enumerate(conds))
    cargs = "".join(f" c{i + 1}" for i in range(len(conds)))
    segcall = (
        f"segS_{pc} L g {' '.join(pargs)} (Control.facts P L g w d.c)\n"
        f"      (Control.facts P L g w {cnew})\n"
        f"      (facts_keys rfl) (facts_sub rfl (by\n"
        f"        show ∀ r ∈ Control.ctlLive (Site.{nxt[1:]}).pc, r ∈ Control.ctlLive d.c.site.pc\n"
        f"        rw [hs]; decide +kernel))" + cargs
    )
    common = (
        f"(pc := {pc}) (pc' := {seg['end']}) (by rw [hs]; rfl) rfl\n"
        f"    (c' := {cnew}) (b' := d.b) (by rw [hs]; decide)"
    )
    he1 = "(fun _ => rfl)" if reset else "(fun h => h)"
    hel = "(fun _ => by simp [Control.elems])" if reset else "(fun h => by simp [Control.elems, h])"
    tail = (
        f"(by rw [hs]; decide) hok\n"
        f"    (fun e => by simp [Control.succ, hs]) (by simp [succOk, hs])\n"
        f"    (fun _ => by simp [record, hs]) {he1}\n"
        f"    {hel} ?_ e\n"
    )
    seg_part = (
        f"  · have h := {segcall}\n"
        f"    have e1 : wF (scX L) d.c.site d.b = {F} := by rw [hs]; rfl\n"
        f"    rw [e1]\n    exact h\n"
    )
    if kind == "nx":
        hadv = re.search(r"\(fun _ _ _ hf => (\w+) hf\)", ds).group(1)
        body = (
            f"  refine skW_nx {common}\n    (by rw [hs]; exact Flow.code_{pc}) ?_ {tail}"
            f"  · intro t e u hf\n    rw [hs] at hf\n    exact {hadv} hf\n" + seg_part
        )
    elif kind == "st":
        body = (
            f"  refine skW_st {common}\n    (by rw [hs]; exact Flow.code_{pc}) rfl rfl {tail}"
            + seg_part
        )
    elif kind in ("ld1", "ld2"):
        return gen_ld(pc, kind, site, nxt, args, seg, cnew, reset)
    else:
        raise ValueError(kind)
    head = (
        f"/-- The strict step at pc {pc}. -/\ntheorem sk_{pc} (d : D) (hs : d.c.site = ({site}))\n"
        f"    (hok : d.ok = true){hyps} (e : Event) :\n    (code P L g w).StepFor d e := by\n"
    )
    return head + body


def tail_ld1(er, nxt):
    if not er:
        return "  exact h\n"
    return (
        f"  obtain ⟨n, h⟩ := h\n  refine ⟨n, h.weaken_end fun R hR => ?_⟩\n"
        f"  have h2 := (holds_append _ _ _).mp hR\n"
        f"  refine (holds_append _ _ _).mpr ⟨facts_of_erase (by\n"
        f"    show {er} ∈ Control.ctlLive (Site.{nxt[1:]}).pc\n    decide +kernel) ?_ h2.1, h2.2⟩\n"
        f"  have h3 := holds_mem h2.2 (r := {er}) (v := Gen.mld_v577 fun _ => .pred false)\n"
        f"    (by simp [f_vote, Gen.mld_facts1, Gen.mld_v577])\n"
        f"  refine h3.trans (congrArg some ?_)\n"
        f"  unfold Control.valueOf Control.values Gen.mld_v577\n  rfl\n"
    )


def gen_ld(pc, kind, site, nxt, args, seg, cnew, reset):
    """The load kinds: the conditions are about the value `v` the event reads."""
    args = [re.sub(r"\bloadVal bs\b", "v", re.sub(r"\ba0\b", "d.c.a0", a)) for a in args]
    pargs = [a if a.startswith("(") else f"({a})" for a in args]
    cs = [subst(c, seg["names"], pargs) for c in seg["conds"]]
    F = subst(seg["F"], seg["names"], pargs)
    cd = " ∧ ".join(f"({c})" for c in cs) if len(cs) > 1 else cs[0]
    hold = f"(d.c.el ≠ 0 → {cd})" if kind == "ld2" else cd
    proj = ["c"] if len(cs) == 1 else ["c.1", "c.2"]
    cargs = "".join(" " + x for x in proj)
    segcall = (
        f"segS_{pc} L g {' '.join(pargs)} (Control.facts P L g w d.c)\n"
        f"      (Control.facts P L g w {cnew})\n"
        f"      (facts_keys rfl) (facts_sub rfl (by\n"
        f"        show ∀ r ∈ Control.ctlLive (Site.{nxt[1:]}).pc, r ∈ Control.ctlLive d.c.site.pc\n"
        f"        rw [hs]; decide +kernel))" + cargs
    )
    er = ERASE.get(pc)
    if er:
        segcall = (
            f"segS_{pc} L g {' '.join(pargs)} (Control.facts P L g w d.c)\n"
            f"      (factsFrom ((Control.ctlLive (Site.{nxt[1:]}).pc).erase {er})\n"
            f"        (Control.valueOf P L g w {cnew}))\n"
            f"      factsFrom_keys (facts_sub_erase rfl (by\n"
            f"        show ∀ r ∈ (Control.ctlLive (Site.{nxt[1:]}).pc).erase {er},\n"
            f"          r ∈ Control.ctlLive d.c.site.pc\n"
            f"        rw [hs]; decide +kernel))" + cargs
        )
    cdfun = f"(Cd := fun v => {cd})"
    head = (
        f"/-- The strict step at pc {pc}. -/\ntheorem sk_{pc} (d : D) (hs : d.c.site = ({site}))\n"
        f"    (hok : d.ok = true) (e : Event)\n    (hcd : ∀ x bs, e.kind = .rd x bs → ∃ v,"
        f" rebuild 3 bs = .ok v ∧ {hold}) :\n    (code P L g w).StepFor d e := by\n"
    )
    if kind == "ld1":
        r = LD1_REG[pc]
        body = (
            f"  refine skW_ld1 (pc := {pc}) (pc' := {seg['end']}) (mk := fun v => {{ d.b with {LD1_FIELD[pc]} := v }})\n"
            f"    (r := {r}) {cdfun} hcd (by rw [hs]; rfl) rfl (c' := {cnew}) (by rw [hs]; decide)\n"
            f"    (by rw [hs]; exact Flow.code_{pc}) rfl rfl rfl rfl (by rw [hs]; decide) hok\n"
            f"    (fun x bs => by simp [Control.succ, hs, Control.dataRd]) (by simp [succOk, hs])\n"
            f"    (fun x bs v hv => by simp [record, hs, loadVal_ok hv]) (fun h => h)\n"
            f"    (fun h => by simp [Control.elems, h])\n"
            f"    (facts_fresh (by rw [hs]) (by decide +kernel)\n"
            f"      (fun q hq h => by\n        rw [hs] at hq\n"
            f"        exact hoff_of (F := wF (scX L) ({site}) d.b) (ds := [{r}]) (by kernel_rfl) q hq\n"
            f"          (by simp [h]))) ?_\n"
            f"  intro v c\n  have h := {segcall}\n"
            f"  have e1 : wF (scX L) d.c.site d.b ++ [({r}, v)] = {F} := by rw [hs]; rfl\n"
            f"  rw [← e1, ← List.append_assoc] at h\n" + tail_ld1(er, nxt)
        )
        # the segment call takes the conditions from hv
        body = body.replace("    hv\n  have e1", "    hv\n  have e1")
    else:
        k = int(re.search(r"\.pld (\d)", site).group(1))
        r0, r1 = 3146 + 4 * k, 3148 + 4 * k
        mk = f"fun v => pwSet d.b {k} d.c.a0 v"
        body = (
            f"  refine skW_ld2 (pc := {pc}) (pc' := {seg['end']}) (mk := {mk})\n"
            f"    (r0 := {r0}) (r1 := {r1}) {cdfun} hcd hs rfl rfl\n"
            f"    (c' := {cnew}) Flow.code_{pc} rfl rfl rfl rfl (by decide) hok\n"
            f"    (fun he0 x bs v hv => by simp [Control.succ, hs, he0, hv, Except.toOption])\n"
            f"    (fun he0 x bs => by simp [Control.succ, hs, he0]) (fun he0 => by simp [succOk, hs, he0])\n"
            f"    (fun x bs v he0 hv => by simp [record, hs, he0, loadVal_ok hv, pwSet]) rfl\n"
            f"    (by show 0 < Control.elems ({nxt}); decide)\n"
            f"    (facts_fresh_l (by rw [hs]) (by decide +kernel)\n"
            f"      (fun q hq => hoff_of (F := wF (scX L) ({site}) d.b) (ds := [{r0}, {r1}])\n"
            f"        (by kernel_rfl) q (by rw [hs] at hq; exact hq))) ?_\n"
            f"  intro v c\n  have h := {segcall}\n"
            f"  have e1 : wF (scX L) d.c.site d.b ++ [({r0}, d.c.a0), ({r1}, v)] = {F} := by\n"
            f"    rw [hs]; rfl\n"
            f"  rw [← e1, ← List.append_assoc] at h\n  exact h\n"
        )
    return head + body


def wrap(text):
    out = []
    for line in text.split("\n"):
        ind = len(line) - len(line.lstrip())
        while len(line) > 98:
            cut = line.rfind(" ", ind + 10, 98)
            out.append(line[:cut])
            line = " " * (ind + 4) + line[cut + 1 :]
        out.append(line)
    return "\n".join(out)


def main():
    dsb = blocks(["DataSteps0", "DataSteps1", "EpiOut0", "EpiOut1", "EpiOut2", "EpiOut3"])
    segb = blocks(SEGS)
    dsd = {k[2]: v for k, v in dsb.items() if k[1] == "ds"}
    sgd = {k[2]: v for k, v in segb.items() if k[1] == "segS"}
    for out, pcs in OUT.items():
        parts = [gen(pc, dsd[pc], parse_seg(sgd[pc])) for pc in sorted(pcs)]
        imps = "".join(f"public import {NS}.Gen.{s}\n" for s in SEGS)
        head = (
            "-- SPDX-License-Identifier: Apache-2.0\n-- Generated by Kernels/FlashMlaSparseDecodeH64/Gen/"
            "w0step_gen.py; do not edit.\n-- domain: valid-rows\nmodule\n\n"
            f"public import {NS}.Data.StepKinds\npublic import {NS}.Data.StepLd2\n{imps}\n@[expose] public section\n\n"
            "namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data\n"
            "open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64\n\n"
            "noncomputable section\n\nvariable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}\n\n"
        )
        (GEN / f"{out}.lean").write_text(
            wrap(head + "\n".join(parts))
            + "\nend\nend PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data\n"
        )


if __name__ == "__main__":
    main()
