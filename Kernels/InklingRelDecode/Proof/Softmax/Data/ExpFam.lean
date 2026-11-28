-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsMid
public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartClass
public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartRegion
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The exponent window's facts are kept by the sites of the round

From the shuffle of pc 2234 to the barrier of pc 2326 and the store of pc 2328, the events of the
round write none of the exponentials' registers and the code up to the next event is in a region
that writes none (`ivsX`). The words the facts are made of (`xV`) are those of the state's
predecessor, so the successor's facts are the site's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem xV_congr {d d' : D} (hm : m0 d = m0 d') (hx : d.v.mx = d'.v.mx) (hi : d.c.i = d'.c.i)
    (hc : d.v.cur = d'.v.cur) (hl : d.v.ld = d'.v.ld) (hs : d.v.s = d'.v.s) :
    xV e L g d = xV e L g d' := by
  funext r
  simp only [xV, w1V, canon, hm, hx, hi, hc, hl, hs]

/-- The sites whose events change none of the words that the exponent window's inputs are made
of: the exponentials' sites, the barrier and the store. -/
def plainX : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .ldO | .waitLdO | .bar24 | .stO | .bar20 | .tmemSt => true
  | _ => false

/-- The sites of the round that keep the exponentials. -/
def keepX : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .ldO | .waitLdO | .bar24 | .stO => true
  | _ => false

theorem record_x {d : D} (ev : Event) (z : Site) (h : plainX d.c.site = true) :
    (record L d ev z).m = d.v.m ∧ (record L d ev z).mx = d.v.mx ∧ (record L d ev z).mp = d.v.mp ∧
    (record L d ev z).cur = d.v.cur ∧ (record L d ev z).ld = d.v.ld ∧
    (record L d ev z).s = d.v.s := by
  unfold record
  split <;> simp_all [plainX]

theorem next_i {d : D} {ev : Event} {c' : Control.D}
    (hn : Control.next e L g d.c ev = some (some c')) (h1 : d.c.site ≠ .bar21)
    (h2 : d.c.site ≠ .arrive) : c'.i = d.c.i := by
  cases hs : d.c.site <;> simp only [Control.next, hs] at hn h1 h2 <;> (try split at hn) <;>
    (try split at hn) <;> simp only [Option.some.injEq, reduceCtorEq] at hn <;>
    (try subst hn) <;> simp_all

theorem keep_inRound {s : Site} (h : keepX s = true) : inRound s = true := by
  cases s <;> simp_all [keepX, inRound]

theorem keep_plain {s : Site} (h : keepX s = true) : plainX s = true := by
  cases s <;> simp_all [keepX, plainX]

theorem keep_succ {s z : Site} (h : keepX s = true) (hz : z ∈ succs s) :
    inRound z = true ∧ plainX s = true ∧ z ≠ .bar20 ∧ z ≠ .tmemSt := by
  refine ⟨?_, keep_plain h, ?_, ?_⟩ <;> cases s <;> simp_all [keepX, succs, inRound] <;>
    rcases hz with rfl | rfl <;> simp_all

/-- **The words the exponent window's inputs are made of do not change** at a site that keeps
the exponentials. -/
theorem xV_keep {d d' : D} {ev : Event} (hk : keepX d.c.site = true)
    (hn : succ e L g d ev = some (some d')) : xV e L g d = xV e L g d' := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨hr, hp, h20, htm⟩ := keep_succ hk (next_mem (e := e) (L := L) (g := g) hnc)
  obtain ⟨r1, r2, -, r4, r5, r6⟩ := record_x (L := L) (d := d) ev c'.site hp
  have hb : d.c.site ≠ .bar21 ∧ d.c.site ≠ .arrive := by cases s : d.c.site <;> simp_all [keepX]
  refine xV_congr ?_ r2.symm (next_i hnc hb.1 hb.2).symm r4.symm r5.symm r6.symm
  have h1 : d.c.site ≠ .bar20 ∧ d.c.site ≠ .tmemSt := by cases s : d.c.site <;> simp_all [keepX]
  simp only [m0, h1.1, h1.2, h20, htm, or_self, ite_false]
  exact r1.symm

theorem xF_keep {d d' : D} {ev : Event} (hk : keepX d.c.site = true)
    (hn : succ e L g d ev = some (some d')) : xF e L g d' = xF e L g d := by
  have hx := xV_keep hk hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨hr, -, -, -⟩ := keep_succ hk (next_mem (e := e) (L := L) (g := g) hnc)
  unfold xF xF0 xE
  rw [← hx]
  simp [hr, keep_inRound hk]

theorem xF_round {d : D} (hr : inRound d.c.site = true) (hE : ExpIn (xV e L g d)) :
    xF e L g d = factsFrom xKeys (xE e L g d) := by
  simp only [xF, xF0, hr, hE, ite_true]

theorem xF_bar20 {d : D} (hs : d.c.site = .bar20) (hE : ExpIn (xV e L g d)) :
    xF e L g d = factsFrom kB20 (vP1 (xE e L g d)) := by
  simp [xF, xF0, hs, hE, inRound]

theorem xF_tmemSt {d : D} (hs : d.c.site = .tmemSt) (hE : ExpIn (xV e L g d)) :
    xF e L g d = factsFrom kTm (vP2 (vP1 (xE e L g d))) := by
  simp [xF, xF0, hs, hE, inRound]

theorem xF_no {d : D} (hE : ¬ExpIn (xV e L g d)) : xF e L g d = [] := by simp [xF, hE]

/-- The constants of the first state are the entry's. -/
theorem constF_init (e : Entry) (L : Launch) (g : Nat) : constF e L g {} = startF e := by
  simp [constF, derF, pF, wF, wFS, w1F, xF, xF0, inRound, wP, wN, wordF, lF, lFS]

/-- The exponent window's facts hold wherever the machine's facts do. -/
theorem atS_xF {d : D} {R : Nat → Option Value} (h : Holds R ((codeS e L g).facts d)) :
    Holds R (xF e L g d) := by
  obtain ⟨-, -, -, h⟩ := atS_holds h
  exact ((holds_append _ _ _).mp h).2

/-- The region the code after a site of the round runs in: the sites' code but the jumps to the
update. -/
def ivsX : List (Nat × Nat) := [(2238, 18), (2260, 70)]

/-- The checks of a site that keeps the exponentials. -/
def siteX (s : Site) : Bool :=
  inIvs ivsX s.pc && inIvs ivsX (s.pc + 1) && !Assumptions.emuSites.contains s.pc &&
  (match kernel.code[s.pc]? with
    | some ins => xKeys.all fun r => !(eventWrites ins.op).contains r
    | none => true)

theorem region_X : regionH kernel Lib.hooks ivsX xKeys = true := by decide +kernel
theorem region_nil : regionH kernel Lib.hooks ivsX [] = true := by decide +kernel

theorem siteX_ok (s : Site) (h : keepX s = true) : siteX s = true := by
  cases s <;> first | (revert h; decide +kernel) | simp [keepX] at h

open Classical in
/-- **The exponent window's facts are kept** by the sites of the round that write none of them. -/
theorem x_keep {d : D} (hk : keepX d.c.site = true) : DataStep (codeS e L g) (xF e L g) d := by
  have ok := siteX_ok d.c.site hk
  simp only [siteX, Bool.and_eq_true, Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
  have hkeys : (xF e L g d).map Prod.fst = if ExpIn (xV e L g d) then xKeys else [] := by
    simp only [xF, xF0, keep_inRound hk, ite_true]
    split_ifs <;> simp [factsFrom_keys]
  have key : DataStep (codeS e L g) (xF e L g) d :=
    DataStep.constAny (C := codeS e L g) (sF := xF e L g) (d := d) (A := Assumptions.all)
      (tab := Lib.hooks) (ivs := ivsX) Lib.rulesFrame hooks_any
      (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩ (fun R h => atS_xF h)
      (fun ins hc => ?_) (by rw [hkeys]; split_ifs; exacts [region_X, region_nil]) ?_
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    rw [hkeys]
    split_ifs
    · exact h4
    · rfl
  · intro ev d' hn x hx
    rw [xF_keep hk (show succ e L g d ev = some (some d') from hn)] at hx
    exact hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
