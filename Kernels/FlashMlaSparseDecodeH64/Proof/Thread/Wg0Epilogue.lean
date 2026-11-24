-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputNumeric
public import Lemmas.Flow.Bar
import Lemmas.Flow.SegChain
import Lemmas.Flow.RoleTemplates
import Lemmas.Flow.EventCont
import Lemmas.Flow.FloatRead
import Lemmas.Flow.Scalars

@[expose] public section

/-! # The softmax warpgroup's output epilogue -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

private def epiFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) :
    List (Nat × Value) :=
  factsFrom ((Flow.live pc).filter tracked.contains) (valueOf P L g d)

private theorem outputGroups : List.finRange 4 = [0, 1, 2, 3] := rfl

macro "epi_values" : tactic => `(tactic|
  (simp only [valueOf, Nat.reduceLeDiff, Nat.reduceLT, true_and, false_and,
    and_true, and_false, ite_false, ite_true]
   try simp only [outputIndex, outputGroups, outputFirst, stageFirst, List.findSome?_cons,
    List.findSome?_nil, List.getD_cons_zero, List.getD_cons_succ, Fin.val_ofNat,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceSub, Nat.reduceDiv,
    Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceAdd, Nat.reduceMul, true_and, false_and,
    and_true, and_false, ite_false, ite_true]
   try wg0_values))

private theorem epiAtD {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : At t d.site.pc (epiFacts P L g d d.site.pc)) (hsub : d.sub = 0) :
    (code P L g).AtD d t :=
  ⟨h.1, h.2.1.trans hsub.symm, h.2.2.1.trans (siteAcc_nil d hsub).symm,
    h.2.2.2.1, h.2.2.2.2⟩

private theorem epiInv {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d)
    {s : Site} (hd : d.site.inEpilogue = true) (hrow : d.site.needsRowTotal = true)
    (hs : s.inEpilogue = true) (he : s = .exit → warpOf L g = 0) :
    Inv P L g { d with site := s, sub := 0 } := by
  apply inv_setSite h s (fun _ => h.epilogueLast hd) _ _ he _ (fun _ => h.rowTotal hrow) _
  · intro hr
    cases s <;> simp [Site.inEpilogue, Site.inRescale] at hs hr
  · rintro ⟨a, k, hk⟩
    rw [hk] at hs
    cases hs
  · rintro (hh | hh) <;> rw [hh] at hs <;> cases hs
  · intro hx
    cases s <;> simp [Site.inEpilogue, Site.needsExchangeReady] at hs hx

section
variable {P : Params} {L : Launch} {g : Nat}

private theorem commit_tail {d : D} {u : TState} (h : At u 1833 (epiFacts P L g d 1832)) :
    ∃ v, run kernel asms L g 2 u = some v ∧ At v 1835 (epiFacts P L g d 1835) := by
  unfold epiFacts at h ⊢
  seg_fp h using (try epi_values); norm_bits

/-- The bulk commit is followed by the two operands of the CTA's final barrier. -/
theorem step_commit (d : D) (hd : d.site = .commit) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = 1832 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1832)
    have he := fires_bulkCommit hf
    have hu : u = PTX.next t := Option.some.inj hf.2
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hstart := at_next_of hat hpc hsub
    rw [← hu] at hstart
    obtain ⟨v, hr, hv⟩ := commit_tail (d := d) hstart
    let d' : D := { d with site := .everyone, sub := 0 }
    have hi : Inv P L g d' :=
      epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (by intro h; cases h)
    refine Or.inl (Or.inr ⟨d', v, ?_, run_rtg hr, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', hsub]
    · exact epiAtD hv rfl

/-- The closing barrier is a full-CTA synchronization. -/
theorem event_everyone {d : D} {t : TState} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD d t) (hd : d.site = .everyone) :
    eventTmpl asms L g t (.barSyncN (.reg 2425) (.reg 2426) false) =
      .bar 12 (PTX.next t) none .sync := by
  have hr1 := reg_value hat (r := 2425) (by rw [hd]; decide +kernel)
  have hr2 := reg_value hat (r := 2426) (by rw [hd]; decide +kernel)
  have h12 : readBits L g t 32 (.reg 2425) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 (by simpa [valueOf, table, PTX.Flow.lookupLit] using hr1) (by decide)
  have h384 : readBits L g t 32 (.reg 2426) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 (by simpa [valueOf, table, PTX.Flow.lookupLit] using hr2) (by decide)
  simp [eventTmpl, barTmpl, h12, h384, hpre.block]

private theorem everyone_dealloc_tail {d : D} {u : TState} (hw : warpOf L g = 0)
    (h : At u 1836 (epiFacts P L g d 1835)) :
    ∃ v, run kernel asms L g 4 u = some v ∧ At v 1840 (epiFacts P L g d 1840) := by
  let F := epiFacts P L g d 1835
  obtain ⟨u1, hr1, ha1⟩ : ∃ u1, run kernel asms L g 1 u = some u1 ∧
      At u1 1837 ((129, .pred false) :: F) := by
    simp only [F, epiFacts] at h ⊢
    seg_fp h using
      wg0_values
      rw [hw]
      rfl
  have hL : ∀ a ∈ asms, a.localRule L g u1 (.bra 3611 false) = none := by
    intro a ha
    exact Thread.asms_localRule_bra (t := u1) (by rw [ha1.1]; decide)
      (by rw [ha1.1]; decide) a ha
  obtain ⟨u2, hr2, ha2⟩ := run_bra Flow.code_1837 false ha1 ha1.2.2.2.2.1 hL (by seg_free_pc)
  have ha2' : At u2 1838 ((129, .pred false) :: F) := ha2
  obtain ⟨u3, hr3, ha3⟩ : ∃ u3, run kernel asms L g 2 u2 = some u3 ∧
      At u3 1840 (epiFacts P L g d 1840) := by
    simp only [F, epiFacts] at ha2' ⊢
    seg_fp ha2' using (try epi_values); norm_bits
  exact ⟨u3, run_comp (run_comp hr1 hr2) hr3, ha3⟩

/-- Warp zero prepares the Tensor Memory deallocation after the closing barrier. -/
theorem step_everyone {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .everyone)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = 1835 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1835)
    rw [event_everyone hpre hat hd] at hf
    obtain ⟨he, hu⟩ := hf
    rw [he]
    by_cases hw : warpOf L g = 0
    · have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
      have hstart := at_next_of hat hpc hsub
      rw [← Option.some.inj hu] at hstart
      obtain ⟨v, hr, hv⟩ := everyone_dealloc_tail (d := d) hw hstart
      let d' : D := { d with site := .exit, sub := 0 }
      have hi : Inv P L g d' := epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (fun _ => hw)
      refine Or.inl (Or.inr ⟨d', v, ?_, run_rtg hr, ?_, hi⟩)
      · simp [next, nextSite, hd, hw, d', hsub]
      · exact epiAtD hv rfl
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, hw]))

def epiBarIdReg (j : Fin 4) : Nat := [1906, 2077, 2247, 2416].getD j.val 0

def epiBarCountReg (j : Fin 4) : Nat := [1907, 2078, 2150, 2417].getD j.val 0

theorem stageFence_code (j : Fin 4) :
    kernel.code[(Site.stageFence j).pc]? =
      some ⟨none, .fence (.proxy (.async (some (.shared .cta))))⟩ := by
  fin_cases j
  · exact Flow.code_1339
  · exact Flow.code_1499
  · exact Flow.code_1657
  · exact Flow.code_1814

private theorem stageFence_tail {d : D} (j : Fin 4) :
    Seg kernel asms L g ((Site.epiBar j).pc - ((Site.stageFence j).pc + 1))
      ((Site.stageFence j).pc + 1) (epiFacts P L g d (Site.stageFence j).pc)
      (Site.epiBar j).pc (epiFacts P L g d (Site.epiBar j).pc) := by
  fin_cases j
  all_goals intro u h
  all_goals unfold epiFacts at h ⊢
  all_goals seg_fp h using (try epi_values); norm_bits

/-- Publishing one staging group forms the operands of the warpgroup barrier. -/
theorem step_stageFence (d : D) {j : Fin 4} (hd : d.site = .stageFence j) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.stageFence j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (stageFence_code j))
    obtain ⟨he, hu⟩ := fires_fence_proxy hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hstart := at_next_of hat hpc hsub
    rw [← Option.some.inj hu] at hstart
    obtain ⟨v, hr, hv⟩ := stageFence_tail (d := d) j u hstart
    let d' : D := { d with site := .epiBar j, sub := 0 }
    have hi : Inv P L g d' :=
      epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (by intro h; cases h)
    refine Or.inl (Or.inr ⟨d', v, ?_, run_rtg hr, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', hsub]
    · exact epiAtD hv rfl

/-- The site following a completed output group. -/
def afterOutputGroup (j : Fin 4) : Site :=
  if h : j.val + 1 < 4 then .oLoad ⟨j.val + 1, h⟩ else .commit

def outputGroupPC (j : Fin 4) : Nat := (Site.tmaStore j).pc + 1

private theorem warpGtOne {w : Nat} (hw : w < 4) :
    compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 w)) (truncBits 32 (BitVec.ofInt 64 1)) =
      decide (2 ≤ w) := by
  interval_cases w <;> decide

private theorem afterOutputGroup_tail {d : D} (j : Fin 4) (_hw : warpOf L g < 4) :
    Seg kernel asms L g ((afterOutputGroup j).pc - outputGroupPC j)
      (outputGroupPC j) (epiFacts P L g d (outputGroupPC j))
      (afterOutputGroup j).pc (epiFacts P L g d (afterOutputGroup j).pc) := by
  fin_cases j
  all_goals intro u h
  all_goals unfold epiFacts at h ⊢
  all_goals seg_fp h using
    try epi_values
    first
    | exact congrArg Value.pred (warpGtOne _hw)
    | norm_bits

def outputTmaOp (j : Fin 4) : Op :=
  .cpTensorStore (.reg 3832)
    [.reg ([1914, 2083, 2252, 2422].getD j.val 0),
      .reg ([1915, 2084, 2253, 2423].getD j.val 0), .reg 459, .reg 460]
    ([1913, 2082, 2251, 2421].getD j.val 0) 0 none .tile none

theorem outputTma_code (j : Fin 4) :
    kernel.code[(Site.tmaStore j).pc]? = some ⟨none, outputTmaOp j⟩ := by
  fin_cases j
  · exact Flow.code_1358
  · exact Flow.code_1516
  · exact Flow.code_1673
  · exact Flow.code_1831

private theorem fires_outputTma {L : Launch} {g : Nat} {j : Fin 4} {t u : TState}
    {pc : Nat} {e : Event} (hf : Fires pc (eventTmpl asms L g t (outputTmaOp j)) e (some u)) :
    ∃ a spec, e = ⟨pc, .tensorStore a spec⟩ ∧ u = PTX.next t := by
  unfold outputTmaOp at hf
  simp only [eventTmpl, tensorStoreTmpl] at hf
  generalize hs : tensorStoreSpec L g t (.reg 3832)
    [.reg ([1914, 2083, 2252, 2422].getD j.val 0),
      .reg ([1915, 2084, 2253, 2423].getD j.val 0), .reg 459, .reg 460]
    ([1913, 2082, 2251, 2421].getD j.val 0) 0 none .tile none = x at hf
  cases x with
  | error why => simp [ofExec, Fires, Bind.bind, Except.bind] at hf
  | ok data =>
    rcases data with ⟨a, s⟩
    change Fires pc (.tensorStore a s (PTX.next t)) e (some u) at hf
    exact ⟨a, s, hf.1, Option.some.inj hf.2⟩

private theorem outputGroup_live (j : Fin 4) :
    ∀ reg ∈ (Flow.live (outputGroupPC j)).filter tracked.contains,
      reg ∈ (Flow.live (Site.tmaStore j).pc).filter tracked.contains := by
  have h : ((Flow.live (outputGroupPC j)).filter tracked.contains).all
      (fun reg => ((Flow.live (Site.tmaStore j).pc).filter tracked.contains).contains reg) =
        true := by
    fin_cases j <;> decide +kernel
  simpa using List.all_eq_true.mp h

/-- A TMA issue continues to the next chunk, or to the bulk commit after the final issue. -/
theorem step_tmaStore (d : D) {j : Fin 4} (hd : d.site = .tmaStore j) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.tmaStore j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputTma_code j))
    obtain ⟨a, s, he, hu⟩ := fires_outputTma (j := j) hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hstart := at_next_of hat hpc hsub
    rw [← hu] at hstart
    have hstart' : At u (outputGroupPC j) (epiFacts P L g d (outputGroupPC j)) :=
      hstart.mono (holds_factsFrom_mono hstart.2.2.2.2 (outputGroup_live j))
    obtain ⟨v, hr, hv⟩ := afterOutputGroup_tail (d := d) j inv.warpLt u hstart'
    let d' : D := { d with site := afterOutputGroup j, sub := 0 }
    have hnext : (afterOutputGroup j).inEpilogue = true := by
      unfold afterOutputGroup
      split <;> rfl
    have hnextex : afterOutputGroup j ≠ .exit := by
      unfold afterOutputGroup
      split <;> intro heq <;> cases heq
    have hi : Inv P L g d' :=
      epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) hnext (fun h => (hnextex h).elim)
    refine Or.inl (Or.inr ⟨d', v, ?_, run_rtg hr, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', afterOutputGroup, hsub]
    · exact epiAtD hv rfl

def epiBarOp (j : Fin 4) : Op :=
  .barSyncN (.reg (epiBarIdReg j)) (.reg (epiBarCountReg j)) true

theorem epiBar_code (j : Fin 4) :
    kernel.code[(Site.epiBar j).pc]? = some ⟨none, epiBarOp j⟩ := by
  fin_cases j
  · exact Flow.code_1342
  · exact Flow.code_1502
  · exact Flow.code_1659
  · exact Flow.code_1817

/-- The four publications use barrier nine for all 128 softmax threads. -/
theorem event_epiBar {d : D} {t : TState} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD d t) {j : Fin 4} (hd : d.site = .epiBar j) :
    eventTmpl asms L g t (epiBarOp j) = .bar 9 (PTX.next t) (some 128) .sync := by
  have hr1 := reg_value hat (r := epiBarIdReg j) (by rw [hd]; fin_cases j <;> decide +kernel)
  have hr2 := reg_value hat (r := epiBarCountReg j) (by rw [hd]; fin_cases j <;> decide +kernel)
  have h9 : readBits L g t 32 (.reg (epiBarIdReg j)) = .ok (BitVec.ofNat 64 9) :=
    readBits_b32 (by fin_cases j <;> exact hr1) (by decide)
  have h128 : readBits L g t 32 (.reg (epiBarCountReg j)) = .ok (BitVec.ofNat 64 128) :=
    readBits_b32 (by fin_cases j <;> exact hr2) (by decide)
  simp [epiBarOp, eventTmpl, barTmpl, h9, h128, hpre.block]

private def epiBranchPC (j : Fin 4) : Nat := [1346, 1503, 1660, 1818].getD j.val 0

private def epiBranchPred (j : Fin 4) : Nat := [121, 123, 125, 127].getD j.val 0

private def epiBranchFacts (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4) :
    List (Nat × Value) :=
  (epiBranchPred j, .pred (decide (2 ≤ warpOf L g))) ::
    epiFacts P L g d (epiBranchPC j)

private theorem epiBranch_code (j : Fin 4) :
    kernel.code[epiBranchPC j]? =
      some ⟨some (epiBranchPred j, false), .bra (outputGroupPC j) false⟩ := by
  fin_cases j
  · exact Flow.code_1346
  · exact Flow.code_1503
  · exact Flow.code_1660
  · exact Flow.code_1818

private theorem epiBranch_prefix {d : D} (j : Fin 4) (hw : warpOf L g < 4)
    (hb : L.sharedBase + 222952 < 2 ^ 32) :
    Seg kernel asms L g (epiBranchPC j - ((Site.epiBar j).pc + 1))
      ((Site.epiBar j).pc + 1) (epiFacts P L g d (Site.epiBar j).pc)
      (epiBranchPC j) (epiBranchFacts P L g d j) := by
  have hw0 : warpOf L g < 2 ^ 32 := by omega
  have hw1 : 16384 * warpOf L g < 2 ^ 32 := by omega
  have hL : L.sharedBase < 2 ^ 32 := by omega
  have hs : L.sharedBase + 16384 * warpOf L g < 2 ^ 32 := by omega
  fin_cases j
  all_goals intro u hu
  all_goals unfold epiFacts at hu
  all_goals unfold epiBranchFacts epiFacts
  all_goals seg_fp hu using
    try epi_values
    norm_bits [sb, Nat.add_zero, Nat.mul_comm, Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1,
      Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hs]

private theorem epiBranch_run {d : D} {j : Fin 4} {u : TState}
    (h : At u (epiBranchPC j) (epiBranchFacts P L g d j)) :
    ∃ v, run kernel asms L g 1 u = some v ∧
      At v (if 2 ≤ warpOf L g then outputGroupPC j else epiBranchPC j + 1)
        (epiBranchFacts P L g d j) := by
  have hl : ∀ t : TState, t.pc = epiBranchPC j →
      ∀ a ∈ asms, a.localRule L g t (.bra (outputGroupPC j) false) = none := by
    intro t ht
    exact Thread.asms_localRule_bra (t := t) (by rw [ht]; fin_cases j <;> decide)
      (by rw [ht]; fin_cases j <;> decide)
  have hs := Seg.bra (L := L) (g := g) (pick := decide (2 ≤ warpOf L g))
    (F := epiBranchFacts P L g d j) (epiBranch_code j) (by simp [epiBranchFacts]) hl
    (by fin_cases j <;> seg_free_pc)
  simpa only [decide_eq_true_eq] using hs u h

private theorem epiBranch_skip {d : D} {j : Fin 4} {u : TState}
    (h : At u (outputGroupPC j) (epiBranchFacts P L g d j)) :
    At u (outputGroupPC j) (epiFacts P L g d (outputGroupPC j)) := by
  refine h.mono (holds_factsFrom_mono h.2.2.2.2.2 ?_)
  have hregs : ((Flow.live (outputGroupPC j)).filter tracked.contains).all
      (fun r => ((Flow.live (epiBranchPC j)).filter tracked.contains).contains r) = true := by
    fin_cases j <;> decide +kernel
  simpa using List.all_eq_true.mp hregs

private theorem epiBranch_elect {d : D} {j : Fin 4} {u : TState}
    (h : At u (epiBranchPC j + 1) (epiBranchFacts P L g d j)) :
    ∃ v, run kernel asms L g 3 u = some v ∧
      At v (Site.elect j).pc (epiFacts P L g d (Site.elect j).pc) := by
  unfold epiBranchFacts epiFacts at h
  unfold epiFacts
  fin_cases j <;> seg_fp h using (try epi_values); norm_bits

/-- The barrier's tail branches by warp. Only the two epilogue warps elect an issuer. -/
theorem step_epiBar {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {j : Fin 4}
    (hd : d.site = .epiBar j) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.epiBar j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (epiBar_code j))
    rw [event_epiBar hpre hat hd] at hf
    obtain ⟨he, hu⟩ := hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hstart := at_next_of hat hpc hsub
    rw [← Option.some.inj hu] at hstart
    obtain ⟨v, hvRun, hv⟩ := epiBranch_prefix (d := d) j inv.warpLt (sharedBase_lt hpre) u hstart
    obtain ⟨w, hwRun, hw⟩ := epiBranch_run hv
    have hresume : ∃ z, Relation.ReflTransGen (Tau kernel asms L g) u z ∧
        At z (epiAfterBar L g j).pc (epiFacts P L g d (epiAfterBar L g j).pc) := by
      by_cases hwarp : 2 ≤ warpOf L g
      · simp only [hwarp, ↓reduceIte] at hw
        obtain ⟨z, hzRun, hz⟩ := afterOutputGroup_tail (d := d) j inv.warpLt w (epiBranch_skip hw)
        exact ⟨z, run_rtg (run_comp (run_comp hvRun hwRun) hzRun),
          by simpa only [epiAfterBar, hwarp, ↓reduceIte, afterOutputGroup] using hz⟩
      · simp only [hwarp, ↓reduceIte] at hw
        obtain ⟨z, hzRun, hz⟩ := epiBranch_elect hw
        exact ⟨z, run_rtg (run_comp (run_comp hvRun hwRun) hzRun),
          by simpa only [epiAfterBar, hwarp, ↓reduceIte] using hz⟩
    obtain ⟨v', hr, hv'⟩ := hresume
    let d' : D := { d with site := epiAfterBar L g j, sub := 0 }
    have hi : Inv P L g d' := epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl)
      (by unfold epiAfterBar; split <;> (try split) <;> rfl)
      (by unfold epiAfterBar; split <;> (try split) <;> intro heq <;> cases heq)
    refine Or.inl (Or.inr ⟨d', v', ?_, hr, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', hsub]
    · exact epiAtD hv' rfl

def electionDst (j : Fin 4) : Nat := 4078 + 2 * j.val

def electionPred (j : Fin 4) : Nat := electionDst j + 1

def electionMask (j : Fin 4) : Nat := [1912, 2081, 2250, 2420].getD j.val 0

private def electionBranchPC (j : Fin 4) : Nat := (Site.elect j).pc + 4

private def electionBranchPred (j : Fin 4) : Nat := 122 + 2 * j.val

theorem election_code (j : Fin 4) :
    kernel.code[(Site.elect j).pc]? = some ⟨none, .warp
      ⟨.elect, none, [some (electionDst j), some (electionPred j)], [],
        some (.reg (electionMask j))⟩⟩ := by
  fin_cases j
  · exact Flow.code_1350
  · exact Flow.code_1507
  · exact Flow.code_1664
  · exact Flow.code_1822

private theorem electionBranch_code (j : Fin 4) :
    kernel.code[electionBranchPC j]? =
      some ⟨some (electionBranchPred j, false), .bra (outputGroupPC j) false⟩ := by
  fin_cases j
  · exact Flow.code_1354
  · exact Flow.code_1511
  · exact Flow.code_1668
  · exact Flow.code_1826

private def electedFacts (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4)
    (leader : Nat) : List (Nat × Value) :=
  (electionPred j, .pred (PTX.laneOf L g == leader)) :: (electionDst j, b32 leader) ::
    epiFacts P L g d (Site.elect j).pc

private theorem election_at {d : D} {j : Fin 4} {t u : TState} {leader : Nat}
    (hat : (code P L g).AtD d t) (hd : d.site = .elect j) (hsub : d.sub = 0)
    (hu : u = PTX.next (setReg (setReg t (electionDst j) (b32 leader)) (electionPred j)
      (.pred (PTX.laneOf L g == leader)))) :
    At u ((Site.elect j).pc + 1) (electedFacts P L g d j leader) := by
  have ha := at_next_of hat (congrArg Site.pc hd) hsub
  rw [hu]
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ?_⟩
  have he : ∀ p ∈ epiFacts P L g d (Site.elect j).pc, p.1 ≠ electionDst j := by
    intro p hp heq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    change r = _ at heq
    rw [heq] at hr
    fin_cases j <;> exact (show ¬ _ from by decide +kernel) hr
  have hp : ∀ p ∈ epiFacts P L g d (Site.elect j).pc, p.1 ≠ electionPred j := by
    intro p hmem heq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmem
    change r = _ at heq
    rw [heq] at hr
    fin_cases j <;> exact (show ¬ _ from by decide +kernel) hr
  have hne : electionDst j ≠ electionPred j := by
    unfold electionPred
    omega
  change Holds _ ((electionPred j, .pred (PTX.laneOf L g == leader)) ::
    (electionDst j, b32 leader) :: epiFacts P L g d (Site.elect j).pc)
  refine ⟨Function.update_self .., ?_, ?_⟩
  · change Function.update (Function.update t.regs (electionDst j) (some (b32 leader)))
      (electionPred j) (some (.pred (PTX.laneOf L g == leader))) (electionDst j) = _
    rw [Function.update_of_ne hne, Function.update_self]
  · exact holds_update (holds_update ha.2.2.2.2 he) hp

private def electionBranchFacts (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4)
    (skipIssue : Bool) : List (Nat × Value) :=
  (electionBranchPred j, .pred skipIssue) :: epiFacts P L g d (electionBranchPC j)

private theorem electionBranch_prefix {d : D} (j : Fin 4) (leader : Nat) (skipIssue : Bool)
    (hp : (PTX.laneOf L g == leader) = !skipIssue) :
    Seg kernel asms L g 3 ((Site.elect j).pc + 1) (electedFacts P L g d j leader)
      (electionBranchPC j) (electionBranchFacts P L g d j skipIssue) := by
  cases skipIssue <;> fin_cases j
  all_goals intro u hu
  all_goals unfold electedFacts epiFacts at hu
  all_goals rw [hp] at hu
  all_goals unfold electionBranchFacts epiFacts
  all_goals seg_fp hu using
    try epi_values
    first
    | rfl
    | norm_bits

private theorem electionBranch_run {d : D} {j : Fin 4} {u : TState} {skipIssue : Bool}
    (h : At u (electionBranchPC j) (electionBranchFacts P L g d j skipIssue)) :
    ∃ v, run kernel asms L g 1 u = some v ∧
      At v (if skipIssue then outputGroupPC j else electionBranchPC j + 1)
        (electionBranchFacts P L g d j skipIssue) := by
  have hl : ∀ t : TState, t.pc = electionBranchPC j →
      ∀ a ∈ asms, a.localRule L g t (.bra (outputGroupPC j) false) = none := by
    intro t ht
    exact Thread.asms_localRule_bra (t := t) (by rw [ht]; fin_cases j <;> decide)
      (by rw [ht]; fin_cases j <;> decide)
  exact Seg.bra (pick := skipIssue) (electionBranch_code j) (by simp [electionBranchFacts]) hl
    (by fin_cases j <;> seg_free_pc) u h

private theorem electionBranch_skip {d : D} {j : Fin 4} {u : TState}
    (h : At u (outputGroupPC j) (electionBranchFacts P L g d j true)) :
    At u (outputGroupPC j) (epiFacts P L g d (outputGroupPC j)) := by
  refine h.mono (holds_factsFrom_mono h.2.2.2.2.2 ?_)
  have hregs : ((Flow.live (outputGroupPC j)).filter tracked.contains).all
      (fun r => ((Flow.live (electionBranchPC j)).filter tracked.contains).contains r) = true := by
    fin_cases j <;> decide +kernel
  simpa using List.all_eq_true.mp hregs

set_option maxHeartbeats 4000000 in
private theorem electionBranch_issue {d : D} (j : Fin 4) (hw : warpOf L g < 4)
    (hb : L.sharedBase + 222952 < 2 ^ 32) :
    Seg kernel asms L g ((Site.tmaStore j).pc - (electionBranchPC j + 1))
      (electionBranchPC j + 1) (electionBranchFacts P L g d j false)
      (Site.tmaStore j).pc (epiFacts P L g d (Site.tmaStore j).pc) := by
  have hbase : L.sharedBase + 16384 * warpOf L g < 2 ^ 32 := by omega
  fin_cases j
  all_goals intro u hu
  all_goals unfold electionBranchFacts epiFacts at hu
  all_goals unfold epiFacts
  all_goals seg_fp hu using
    try epi_values
    norm_bits [tmaX, planeAdd, tmaSrc, stageBase, groupOff, stageTileBytes, sb,
      Nat.mod_eq_of_lt hbase, Nat.mul_comm, Nat.mul_add,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Elected lanes compute the physical staging source and folded TMA tile origin. -/
theorem step_electOutput {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {j : Fin 4}
    (hd : d.site = .elect j) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.elect j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (election_code j))
    obtain ⟨mk, instanceId, leader, he, hu⟩ := fires_elect hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have ha := election_at hat hd hsub hu
    have hcore := laneOf_core (g := g) hpre
    by_cases hl : leader = PTX.laneOf L g
    · have hpred : (PTX.laneOf L g == leader) = !false := by simp [hl]
      obtain ⟨v, hr1, hv⟩ := electionBranch_prefix (d := d) j leader false hpred u ha
      obtain ⟨w, hr2, hw⟩ := electionBranch_run hv
      obtain ⟨z, hr3, hz⟩ := electionBranch_issue (d := d) j inv.warpLt (sharedBase_lt hpre) w hw
      let d' : D := { d with site := .tmaStore j, sub := 0 }
      have hi : Inv P L g d' :=
        epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (by intro heq; cases heq)
      refine Or.inl (Or.inr ⟨d', z, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3), ?_, hi⟩)
      · simp [next, nextSite, hd, hsub, he, d', hl.trans hcore]
      · exact epiAtD hz rfl
    · have hpred : (PTX.laneOf L g == leader) = !true := by simp [Ne.symm hl]
      obtain ⟨v, hr1, hv⟩ := electionBranch_prefix (d := d) j leader true hpred u ha
      obtain ⟨w, hr2, hw⟩ := electionBranch_run hv
      obtain ⟨z, hr3, hz⟩ := afterOutputGroup_tail (d := d) j inv.warpLt w (electionBranch_skip hw)
      let d' : D := { d with site := afterOutputGroup j, sub := 0 }
      have hi : Inv P L g d' := epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl)
        (by unfold afterOutputGroup; split <;> rfl)
        (by unfold afterOutputGroup; split <;> intro heq <;> cases heq)
      refine Or.inl (Or.inr ⟨d', z, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3), ?_, hi⟩)
      · simp [next, nextSite, hd, hsub, he, d', ← hcore, hl, afterOutputGroup]
      · exact epiAtD hz rfl

/-- Coordinates of the output box in (column, head, query, batch) order. -/
def outputOrigin (L : Launch) (g : Nat) (j : Fin 4) (i : Fin 4) : Int :=
  [tmaX j.val (warpOf L g), 0, qOf L g, eOf L g].getD i.val 0

/-- The box copied from the warp's swizzled shared tile. -/
def outputSpec (P : Params) (L : Launch) (g : Nat) (j : Fin 4) : TensorStore.Spec :=
  { outer := 3
    descriptor := mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass
    origin := outputOrigin L g j
    sharedBase := shLoc L g (tmaSrc j.val (warpOf L g))
    rows := none
    reduce := none }

private theorem outputMapAddress {d : D} {t : TState} {j : Fin 4} (hat : (code P L g).AtD d t)
    (hd : d.site = .tmaStore j) (hle : P.param1Base + 1024 ≤ 2 ^ 64) :
    tensorMapAddress L g t (.reg 3832) = .ok (P.param1Base + 512) := by
  have hr : t.regs 3832 = some (b64 (P.param1Base + 512)) :=
    reg_value hat (by rw [hd]; fin_cases j <;> decide +kernel)
  have hbits := readBits_b64 (L := L) (g := g) hr (by omega)
  simp [tensorMapAddress, readValue, readReg, hr, b64, hbits]
  omega

/-- The pending output issue has the actual map, folded tile and shared source template. -/
theorem outputTma_known {d : D} {t : TState} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD d t) {j : Fin 4} (hd : d.site = .tmaStore j) (hw : warpOf L g < 4)
    (hq : qOf L g < P.s_q) (he : eOf L g < P.b) :
    eventTmpl asms L g t (outputTmaOp j) =
      .tensorStore (P.param1Base + 512) (outputSpec P L g j) (PTX.next t) := by
  let xr := [1914, 2083, 2252, 2422].getD j.val 0
  let yr := [1915, 2084, 2253, 2423].getD j.val 0
  let sr := [1913, 2082, 2251, 2421].getD j.val 0
  let x := tmaX j.val (warpOf L g)
  let src := L.sharedBase + tmaSrc j.val (warpOf L g)
  have hrx : t.regs xr = some (b32 x) := by
    have hv := reg_value hat (r := xr) (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hry : t.regs yr = some (b32 0) := by
    have hv := reg_value hat (r := yr) (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hq' : t.regs 459 = some (b32 (qOf L g)) :=
    reg_value hat (by rw [hd]; fin_cases j <;> decide +kernel)
  have he' : t.regs 460 = some (b32 (eOf L g)) :=
    reg_value hat (by rw [hd]; fin_cases j <;> decide +kernel)
  have hrs : t.regs sr = some (b32 src) := by
    have hv := reg_value hat (r := sr) (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hxb : x < 2 ^ 31 := by
    fin_cases j <;> simp [x, tmaX, planeAdd] <;> omega
  have hqb : qOf L g < 2 ^ 31 := hq.trans hpre.sqLt
  have heb : eOf L g < 2 ^ 31 := he.trans hpre.bLt
  have hsb : L.sharedBase + sharedBytes ≤ 2 ^ 18 := by rw [hpre.sharedBase]; exact hpre.sharedRange
  have hs : src < 2 ^ 32 := by
    fin_cases j <;> simp [src, tmaSrc, stageBase, groupOff, stageTileBytes, planeAdd] <;> omega
  have hsrc : sharedEffAddr L g t false sr 0 = .ok (outputSpec P L g j).sharedBase :=
    effAddr_b32 hrs hs
  have hmapA := outputMapAddress hat hd hpre.param1Range
  have hmapAlign : (P.param1Base + 512) % 64 = 0 := by have := hpre.param1Align; omega
  have hsrcAlign : (outputSpec P L g j).sharedBase.addr % 128 = 0 := by
    have hb : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
    fin_cases j <;>
      change (L.sharedBase + tmaSrc (Fin.val _) (warpOf L g)) % 128 = 0 <;>
      simp [tmaSrc, stageBase, groupOff, stageTileBytes, planeAdd] <;> omega
  have hv : TensorDescriptor.Valid (outputSpec P L g j).descriptor := by
    apply mapO_valid hpre.outAlign (by decide) (by decide) _
      ⟨hpre.sqPos, by have := hpre.sqLt; omega⟩
      ⟨hpre.bPos, by have := hpre.bLt; omega⟩
    constructor
    · omega
    · have h := hpre.strideRange
      omega
  have hbox : requireBoxAligned (outputSpec P L g j).descriptor (outputOrigin L g j) = .ok () := by
    apply (requireBoxAligned_eq_ok _ _).mpr
    change ((x : Int) * 2) % 16 = 0
    simp [x, tmaX]; omega
  have hnonneg : ∀ i : Fin 4, 0 ≤ outputOrigin L g j i := by
    intro i
    unfold outputOrigin
    exact Int.natCast_nonneg _
  have hreadx := readBits_b32 (L := L) (g := g) hrx (by omega)
  have hready := readBits_b32 (L := L) (g := g) hry (by decide)
  have hreadq := readBits_b32 (L := L) (g := g) hq' (by omega)
  have hreade := readBits_b32 (L := L) (g := g) he' (by omega)
  have hOrigin :
      (fun i : Fin 4 => (BitVec.ofNat 32
        ([BitVec.ofNat 64 x, BitVec.ofNat 64 0, BitVec.ofNat 64 (qOf L g),
          BitVec.ofNat 64 (eOf L g)].getD i.val 0).toNat).toInt) = outputOrigin L g j := by
    have hcoord (a : Nat) (ha : a < 2 ^ 31) :
        (BitVec.ofNat 32 (BitVec.ofNat 64 a).toNat).toInt = (a : Int) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [BitVec.toInt_ofNat', Int.bmod_def]
      have hd : (a : Int) % (2 ^ 32 : Nat) = a := by
        rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
      push_cast at hd ⊢
      rw [hd]
      split_ifs
      · rfl
      · omega
    funext i
    fin_cases i
    · exact hcoord x hxb
    · rfl
    · exact hcoord (qOf L g) hqb
    · exact hcoord (eOf L g) heb
  have hmap : tensorMap L g t (.reg 3832) [.reg xr, .reg yr, .reg 459, .reg 460] .tile =
      .ok (P.param1Base + 512, ⟨3, (outputSpec P L g j).descriptor⟩) := by
    change TensorDescriptor.Valid
      (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass) at hv
    simp [tensorMap, hmapA, hmapAlign, hpre.mapOBind, TensorMode.coordinates, hv,
      bind, Except.bind, pure, Except.pure, outputSpec]
  have hOriginAt := congrFun hOrigin
  change (shLoc L g (tmaSrc j.val (warpOf L g))).addr % 128 = 0 at hsrcAlign
  change requireBoxAligned (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass)
    (outputOrigin L g j) = .ok () at hbox
  change tensorStoreTmpl L g t (.cpTensorStore (.reg 3832) [.reg xr, .reg yr, .reg 459, .reg 460]
    sr 0 none .tile none) = _
  simp only [tensorStoreTmpl, tensorStoreSpec, hmap, hsrc, hsrcAlign, hreadx, hready, hreadq,
    hreade, List.mapM_cons, List.mapM_nil, bind, Except.bind, pure, Except.pure, Option.all_none,
    ↓reduceIte, hOriginAt, hnonneg, forall_const, cachePolicyRead, TensorMode.transfer,
    TensorMode.rowCoordinates, hbox, ofExec, true_or, outputSpec]

/-- A firing output issue names the decoded map, folded tile and swizzled shared source. -/
theorem fires_tmaOutput {d : D} {t : TState} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD d t) {j : Fin 4} (hd : d.site = .tmaStore j) (hw : warpOf L g < 4)
    (hq : qOf L g < P.s_q) (he : eOf L g < P.b) {pc : Nat} {e : Event} {u : Option TState}
    (hf : Fires pc (eventTmpl asms L g t (outputTmaOp j)) e u) :
    e.kind = .tensorStore (P.param1Base + 512) (outputSpec P L g j) := by
  rw [outputTma_known hpre hat hd hw hq he] at hf
  exact congrArg Event.kind hf.1

/-! ## Staging stores -/

/-- The 32 frozen generic stores have one common shape, source order and address formula. -/
def stageAccess (j : Fin 4) (k : Fin 8) : MemAccess where
  kind := .store
  space := none
  sem := .weak
  scope := none
  elem := .int .b 32
  vec := 4
  ext := .same
  nc := false
  noftz := false
  hints := ⟨none, none, none, none, none⟩
  addr := ⟨.reg (2992 + k.val) 64, (groupOff j.val : Int)⟩
  dsts := []
  srcs := (List.range 4).map (fun sub => .reg (stageReg j k.val sub))
  mmio := false

theorem stage_code (j : Fin 4) (k : Fin 8) :
    kernel.code[(Site.oStage j k).pc]? = some ⟨none, .mem (stageAccess j k)⟩ := by
  fin_cases j <;> fin_cases k
  · exact Flow.code_1331
  · exact Flow.code_1332
  · exact Flow.code_1333
  · exact Flow.code_1334
  · exact Flow.code_1335
  · exact Flow.code_1336
  · exact Flow.code_1337
  · exact Flow.code_1338
  · exact Flow.code_1491
  · exact Flow.code_1492
  · exact Flow.code_1493
  · exact Flow.code_1494
  · exact Flow.code_1495
  · exact Flow.code_1496
  · exact Flow.code_1497
  · exact Flow.code_1498
  · exact Flow.code_1649
  · exact Flow.code_1650
  · exact Flow.code_1651
  · exact Flow.code_1652
  · exact Flow.code_1653
  · exact Flow.code_1654
  · exact Flow.code_1655
  · exact Flow.code_1656
  · exact Flow.code_1806
  · exact Flow.code_1807
  · exact Flow.code_1808
  · exact Flow.code_1809
  · exact Flow.code_1810
  · exact Flow.code_1811
  · exact Flow.code_1812
  · exact Flow.code_1813

private theorem stagePtr_swizzled {mem0 : Mem0} (hpre : Pre P L mem0) {k : Nat} (hk : k < 8) :
    stageMask L g k ^^^ stagePtr L g k =
      L.sharedBase + (stageBase + quadOff L g) + 16 * (k ^^^ (head L g % 8)) := by
  let B := L.sharedBase + (stageBase + quadOff L g)
  have hL : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  have hB : B % 128 = 0 := by simp only [B, stageBase, quadOff]; omega
  have hPtr : stagePtr L g k = B + 16 * k := by simp only [stagePtr, B, stageBase]; omega
  rw [stageMask_eq hpre g hk, hPtr, Nat.xor_comm]
  exact swz_xor hB hk (Nat.mod_lt _ (by decide))

/-- The staging address comes from its saved generic pointer. -/
theorem stage_write_addr {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {j : Fin 4} {k : Fin 8}
    (hg : g < L.threads) (hw : warpOf L g < 4)
    (hr : t.regs (2992 + k.val) = some (stageWord L g k.val)) :
    accessLoc L g t (stageAccess j k) = .ok (shLoc L g (stageWrite L g j.val k.val 0)) := by
  let a := stageMask L g k.val ^^^ stagePtr L g k.val
  have ha : a = L.sharedBase + (stageBase + quadOff L g) +
      16 * (k.val ^^^ (head L g % 8)) := stagePtr_swizzled hpre k.isLt
  have hstage : a + groupOff j.val = L.sharedBase + stageWrite L g j.val k.val 0 := by
    rw [ha]
    simp only [stageWrite, quadOff, head]
    omega
  have hsum : a + groupOff j.val < 2 ^ 32 := by
    have hb := sharedBase_lt hpre
    have hh := halfLt hw
    have hh' := head_lt L g
    have hxor := xor_lt_eight k.isLt (Nat.mod_lt (head L g) (by decide : 0 < 8))
    rw [ha]
    fin_cases j <;> simp [stageBase, quadOff, groupOff, stageTileBytes, planeAdd] <;> omega
  have hab : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have hptr := readSharedAddress_ptr (L := L) (g := g) (t := t) (gen := true) (cl := true)
    (w := 64) (off := BitVec.ofNat 64 a) hr (.inr rfl) hg (ctaLt hpre hg) rfl (.inl rfl)
    (.inl rfl) (by rw [hab]; omega)
  rw [hab] at hptr
  have h32 : (a : Int) + (groupOff j.val : Int) < 2 ^ 32 := by exact_mod_cast hsum
  have hn : 0 ≤ (a : Int) + (groupOff j.val : Int) := by omega
  simp only [stageAccess, accessLoc, readReg, hr, stageWord, bind, Except.bind, hptr, hn, h32,
    and_self, ↓reduceIte, pure, Except.pure, shLoc, ctaOf]
  rw [← hstage, ← Int.natCast_add, Int.toNat_natCast]

private theorem stage_write_aligned {mem0 : Mem0} (hpre : Pre P L mem0) (j : Fin 4) (k : Fin 8) :
    (L.sharedBase + stageWrite L g j.val k.val 0) % 16 = 0 := by
  have hb : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  fin_cases j <;> simp [stageWrite, stageBase, groupOff, stageTileBytes, planeAdd] <;> omega

/-- The current staged vector element writes the complete four-byte converted value. -/
theorem event_stageOutput {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {j : Fin 4} {k : Fin 8}
    (hg : g < L.threads) (hw : warpOf L g < 4) (hs : t.sub < 4)
    (hr : t.regs (2992 + k.val) = some (stageWord L g k.val)) {v : Value}
    (hv : t.regs (stageReg j k.val t.sub) = some v) (hb : v.bytes = 4) :
    eventTmpl asms L g t (.mem (stageAccess j k)) =
      .write { loc := shLoc L g (stageWrite L g j.val k.val t.sub), size := 4, elem := t.sub }
        v.toBytes (afterStore t (stageAccess j k).srcs) := by
  have hloc := stage_write_addr (j := j) hpre hg hw hr
  have halign := stage_write_aligned (g := g) hpre j k
  have hacc : accessAcc L g t (stageAccess j k) =
      .ok { loc := shLoc L g (stageWrite L g j.val k.val t.sub), size := 4, elem := t.sub } := by
    rw [accessAcc_of_weak rfl]
    simp only [hloc, bind, Except.bind]
    simp only [stageAccess, DType.width, CacheHints.globalOnly, Nat.reduceDiv,
      Bool.false_or, Option.isSome_none, Nat.reduceBEq, Bool.true_and, Bool.false_and]
    change elemAcc (shLoc L g (stageWrite L g j.val k.val 0)) 4 4 t.sub = _
    unfold elemAcc
    have haddr : (shLoc L g (stageWrite L g j.val k.val 0)).addr % 16 = 0 := halign
    simp only [Nat.reduceMul, haddr, ne_eq, not_true_eq_false, or_false, pure, Except.pure]
    congr 2
    simp [shLoc, Loc.at, stageWrite, Nat.add_assoc]
  have hindex : (stageAccess j k).srcs[t.sub]? = some (.reg (stageReg j k.val t.sub)) := by
    simp [stageAccess, List.getElem?_range hs]
  have ht : memTmpl asms L g t (stageAccess j k) = accessTmpl asms L g t (stageAccess j k) := by
    fin_cases j <;> fin_cases k <;> rfl
  rw [eventTmpl, ht]
  have hk : (stageAccess j k).kind = .store := rfl
  have hwidth : (stageAccess j k).elem.width = 32 := rfl
  simp only [accessTmpl, hk, hacc, hindex, hwidth, readValue,
    readReg, hv, bind, Except.bind, pure, Except.pure, storeValue_of_bytes (w := 32) hb]

private def afterStageWord (j : Fin 4) (k : Fin 8) : Site :=
  if h : k.val + 1 < 8 then .oStage j ⟨k.val + 1, h⟩ else .stageFence j

private theorem afterStageWord_pc (j : Fin 4) (k : Fin 8) :
    (afterStageWord j k).pc = (Site.oStage j k).pc + 1 := by
  fin_cases j <;> fin_cases k <;> rfl

private theorem afterStageWord_live (j : Fin 4) (k : Fin 8) :
    ∀ r ∈ (Flow.live (afterStageWord j k).pc).filter tracked.contains,
      r ∈ (Flow.live (Site.oStage j k).pc).filter tracked.contains := by
  have h : ((Flow.live (afterStageWord j k).pc).filter tracked.contains).all
      (fun r => ((Flow.live (Site.oStage j k).pc).filter tracked.contains).contains r) = true := by
    fin_cases j <;> fin_cases k <;> decide +kernel
  simpa using List.all_eq_true.mp h

private theorem stageReg_live (j : Fin 4) (k : Fin 8) (i : Fin 4) :
    stageReg j k.val i.val ∈ (Flow.live (Site.oStage j k).pc).filter tracked.contains := by
  fin_cases j <;> fin_cases k <;> fin_cases i <;> decide +kernel

private theorem stageReg_value (P : Params) (L : Launch) (g : Nat) (d : D) (j : Fin 4) (k : Fin 8)
    (i : Fin 4) :
    valueOf P L g d (stageReg j k.val i.val) = stagePair P L g d (4 * k.val + i.val) := by
  have hk := k.isLt
  have hi := i.isLt
  exact outputStage_value P L g d j ⟨4 * k.val + i.val, by omega⟩

/-- The staging store's exact four-byte payload at the current vector element. -/
theorem event_oStage {mem0 : Mem0} {d : D} {t : TState} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hat : (code P L g).AtD d t) (hinv : Inv P L g d) {j : Fin 4} {k : Fin 8}
    (hd : d.site = .oStage j k) :
    eventTmpl asms L g t (.mem (stageAccess j k)) =
      .write { loc := shLoc L g (stageWrite L g j.val k.val t.sub), size := 4, elem := t.sub }
        (stagePair P L g d (4 * k.val + t.sub)).toBytes (afterStore t (stageAccess j k).srcs) := by
  have hs : t.sub < 4 := by
    have ht : t.sub = d.sub := hat.2.1
    rw [ht]
    simpa [hd, Site.elems] using hinv.subLt
  have hr := reg_value hat (r := 2992 + k.val)
    (by rw [hd]; fin_cases j <;> fin_cases k <;> decide +kernel)
  have hr' : t.regs (2992 + k.val) = some (stageWord L g k.val) := by
    fin_cases k <;> exact hr
  let i : Fin 4 := ⟨t.sub, hs⟩
  have hv := reg_value hat (r := stageReg j k.val i.val) (by rw [hd]; exact stageReg_live j k i)
  have hv' : t.regs (stageReg j k.val t.sub) = some (stagePair P L g d (4 * k.val + t.sub)) :=
    hv.trans (congrArg some (stageReg_value P L g d j k i))
  exact event_stageOutput hpre hg hinv.warpLt hs hr' hv' rfl

/-- Staging writes the vector in order, and the last element advances to the next vector or
the publication fence. -/
theorem step_oStage {mem0 : Mem0} (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) {j : Fin 4}
    {k : Fin 8} (hd : d.site = .oStage j k) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.oStage j k).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (stage_code j k))
    rw [event_oStage hpre hg hat inv hd] at hf
    obtain ⟨he, hu⟩ := hf
    have hlen : (stageAccess j k).srcs.length = 4 := by simp [stageAccess]
    have hsub : t.sub = d.sub := hat.2.1
    have hcur : t.pc = (Site.oStage j k).pc := hat.1.trans hpc
    have hacc : t.acc = [] := by
      have ha := hat.2.2.1
      change t.acc = siteAcc d at ha
      simpa [siteAcc, hd] using ha
    have hel : d.site.elems = 4 := by rw [hd]; rfl
    rw [he]
    simp only [next, nextSite, hd, writeStep, siteLoc, Site.elemBytes, Site.elems, hsub,
      and_self, ite_true]
    have hu' := Option.some.inj hu
    by_cases hh : d.sub + 1 < 4
    · let d' : D := { d with sub := d.sub + 1 }
      have hi : Inv P L g d' := { inv with subLt := by simpa [d', hel] using hh }
      refine Or.inl (Or.inr ⟨d', u, by simp [hh, d', hd], .refl, ?_, hi⟩)
      rw [hu']
      simp only [afterStore, hlen, hsub, hh, ↓reduceIte]
      refine ⟨hat.1, rfl, ?_, hat.2.2.2.1, hat.2.2.2.2⟩
      change t.acc = siteAcc d'
      simpa [d', siteAcc, hd] using hacc
    · let d' : D := { d with site := afterStageWord j k, sub := 0 }
      have hi : Inv P L g d' := epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl)
        (by unfold afterStageWord; split <;> rfl)
        (by unfold afterStageWord; split <;> simp)
      refine Or.inl (Or.inr ⟨d', u, by simp [hh, d', afterStageWord], .refl, ?_, hi⟩)
      rw [hu']
      simp only [afterStore, hlen, hsub, hh, ↓reduceIte]
      refine ⟨by
        change t.pc + 1 = (afterStageWord j k).pc
        rw [afterStageWord_pc, hcur], rfl,
        hacc.trans (siteAcc_nil d' rfl).symm, hat.2.2.2.1, ?_⟩
      exact holds_factsFrom_mono (show Holds t.regs (epiFacts P L g d (Site.oStage j k).pc) from
          by simpa only [code, facts, epiFacts, hpc] using hat.2.2.2.2)
        (afterStageWord_live j k)

/-! ## Tensor Memory tile loads -/

/-- Tensor Memory column operand of each output group's load. -/
def outputLoadAddrReg (j : Fin 4) : Nat := [1809, 1980, 2150, 2319].getD j.val 0

/-- The four tile loads each deliver 64 f32 words in register order. -/
def outputLoadOp (j : Fin 4) : Op := .tcLd (outputDsts j) (outputLoadAddrReg j) .s32x32b none

theorem outputLoad_code (j : Fin 4) :
    kernel.code[(Site.oLoad j).pc]? = some ⟨none, outputLoadOp j⟩ := by
  fin_cases j
  · exact Flow.code_1201
  · exact Flow.code_1361
  · exact Flow.code_1519
  · exact Flow.code_1676

theorem outputWait_code (j : Fin 4) :
    kernel.code[(Site.oWait j).pc]? = some ⟨none, .tcWaitLd⟩ := by
  fin_cases j
  · exact Flow.code_1202
  · exact Flow.code_1362
  · exact Flow.code_1520
  · exact Flow.code_1677

/-- The reported load reads the column selected by the group register. -/
theorem event_oLoad {mem0 : Mem0} {d : D} {t : TState} (hpre : Pre P L mem0)
    (hat : (code P L g).AtD d t) {j : Fin 4} (hd : d.site = .oLoad j) :
    eventTmpl asms L g t (outputLoadOp j) =
      .tcLd (64 * j.val) 64 .s32x32b (fun words => setRegs (PTX.next t) (outputDsts j) words) := by
  have hr : t.regs (outputLoadAddrReg j) = some (b32 (64 * j.val)) := by
    have hv := reg_value hat (r := outputLoadAddrReg j) (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hblock : L.block % 32 = 0 := by rw [hpre.block]
  have hlen : (outputDsts j).length = 64 := by simp [outputDsts]
  have hsize : TcShape.countOk .s32x32b 64 := by decide
  have haddr : 64 * j.val < 2 ^ 32 := by have := j.isLt; omega
  have hb : (BitVec.ofNat 64 (64 * j.val)).toNat = 64 * j.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hread := readBits_b32 (L := L) (g := g) hr haddr
  have hdata : tcDataAddressOk L g .s32x32b (64 * j.val) = true := by fin_cases j <;> rfl
  have hplain : ∀ s, TcShape.s32x32b ≠ .packed16 s := by intro s h; cases h
  have hwait : asms.any (·.tcLdWait t.pc) = false := rfl
  simp only [outputLoadOp, eventTmpl, tcLdTmpl, hwait, tcTmpl_tcLd_none hplain, hblock, hsize,
    hlen, ↓reduceIte, hread, hb, hdata, Bool.false_eq_true, bind, Except.bind, pure, Except.pure,
    ofExec]

private theorem retained_at_outputWait (j : Fin 4) :
    ∀ r ∈ (Flow.live (Site.oWait j).pc).filter tracked.contains,
      r ∉ outputDsts j →
      r ∈ (Flow.live (Site.oLoad j).pc).filter tracked.contains ∧
        outputIndex outputFirst 64 1 r = none ∧ outputIndex stageFirst 32 3 r = none := by
  have h : ((Flow.live (Site.oWait j).pc).filter tracked.contains).all (fun r =>
      (outputDsts j).contains r ||
        (((Flow.live (Site.oLoad j).pc).filter tracked.contains).contains r &&
          (outputIndex outputFirst 64 1 r).isNone && (outputIndex stageFirst 32 3 r).isNone)) =
        true := by fin_cases j <;> decide +kernel
  intro r hr hn
  have hv := List.all_eq_true.mp h r hr
  simpa [hn, and_assoc] using hv

private theorem at_outputLoad {d : D} {t : TState} {words : List Value} (j : Fin 4)
    (hat : At t (Site.oLoad j).pc (epiFacts P L g d (Site.oLoad j).pc)) (hlen : words.length = 64) :
    At (setRegs (PTX.next t) (outputDsts j) words) (Site.oWait j).pc
      (epiFacts P L g (loadOutput L g d j words) (Site.oWait j).pc) := by
  have hpc : (Site.oWait j).pc = (Site.oLoad j).pc + 1 := by fin_cases j <;> rfl
  have hs := setRegs_skel (PTX.next t) (outputDsts j) words
  refine ⟨hs.1.trans ((At.next hat).1.trans hpc.symm), hs.2.1.trans hat.2.1,
    hs.2.2.1.trans hat.2.2.1, hs.2.2.2.trans hat.2.2.2.1, ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  by_cases hdst : r ∈ outputDsts j
  · have hi : outputFirst j ≤ r ∧ r < outputFirst j + 64 := List.mem_range'_1.mp hdst
    have hidx : r - outputFirst j < words.length := by omega
    have hreg := setRegs_get (ds := outputDsts j) (vs := words) (t := PTX.next t)
      (r := r) (p := r - outputFirst j) (v := words.getD (r - outputFirst j) (b32 0))
      List.nodup_range' (by
        have hlt : r - outputFirst j < 64 := by omega
        simpa only [outputDsts, Nat.one_mul, Nat.add_sub_of_le hi.1] using
          (List.getElem?_range' (s := outputFirst j) (step := 1) hlt)) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some])
    have hr' : outputFirst j + (r - outputFirst j) = r := Nat.add_sub_of_le hi.1
    have hv := outputWord_value P L g (loadOutput L g d j words) j
      ⟨r - outputFirst j, by omega⟩
    change valueOf P L g (loadOutput L g d j words) (outputFirst j + (r - outputFirst j)) =
      words.getD (r - outputFirst j) (b32 0) at hv
    rw [← hv, hr'] at hreg
    exact hreg
  · obtain ⟨hlive, hraw, hstage⟩ := retained_at_outputWait j r hr hdst
    rw [setRegs_other _ _ _ _ hdst]
    have heq : valueOf P L g (loadOutput L g d j words) r = valueOf P L g d r := by
      simp only [valueOf, loadOutput, hraw, hstage]
      rfl
    rw [heq]
    exact holds_mem hat.2.2.2.2 (List.mem_map.mpr ⟨r, hlive, rfl⟩)

/-- The load records all returned words. The explicit wait follows immediately. -/
theorem step_oLoad {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {j : Fin 4} (hd : d.site = .oLoad j)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.oLoad j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputLoad_code j))
    rw [event_oLoad hpre hat hd] at hf
    obtain ⟨words, hwords, he, hu⟩ := hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hat' : At t (Site.oLoad j).pc (epiFacts P L g d (Site.oLoad j).pc) :=
      ⟨hat.1.trans hpc, hat.2.1.trans hsub, hat.2.2.1.trans (siteAcc_nil d hsub),
        hat.2.2.2.1, by simpa only [code, facts, epiFacts, hpc] using hat.2.2.2.2⟩
    have hu' := at_outputLoad j hat' hwords
    have huEq : u = setRegs (PTX.next t) (outputDsts j) words := Option.some.inj hu
    rw [← huEq] at hu'
    let d' := { loadOutput L g d j words with site := .oWait j, sub := 0 }
    have hi : Inv P L g d' := by
      have h := epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) (s := .oWait j)
        rfl (by simp)
      constructor <;> first
        | exact h.wg
        | exact h.warpLt
        | exact h.laneLt
        | exact h.headEq
        | exact h.ring
        | exact h.blockLt
        | exact h.epilogueLast
        | exact h.rescaleArm
        | exact h.subLt
        | exact h.armSite
        | exact h.exitWarp
        | exact h.preloop
        | exact h.rowTotal
        | (intro hsite; simp [d'] at hsite)
    refine Or.inl (Or.inr ⟨d', u, ?_, .refl, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', hsub, loadOutput]
    · exact epiAtD hu' rfl

/-- An output wait runs the finite 64-word conversion before the first staging store. -/
theorem step_oWait {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {j : Fin 4} (hd : d.site = .oWait j)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = (Site.oWait j).pc := congrArg Site.pc hd
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans (outputWait_code j))
    have htm : eventTmpl asms L g t .tcWaitLd = .tc .waitLd (PTX.next t) :=
      tc_waitLd (g := g) (by rw [hpre.block])
    rw [htm] at hf
    obtain ⟨he, hu⟩ := hf
    rw [he]
    by_cases hw : goodOutputWords d.oWords
    · have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
      have hstart := at_next_of hat hpc hsub
      rw [← Option.some.inj hu] at hstart
      obtain ⟨v, hr, hv⟩ := run_outputTile j hstart hw
      let d' : D := { d with site := .oStage j 0, sub := 0 }
      have hi : Inv P L g d' :=
        epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (by intro h; cases h)
      refine Or.inl (Or.inr ⟨d', v, ?_, run_rtg hr, ?_, hi⟩)
      · simp [next, nextSite, hd, d', hsub, hw]
      · exact epiAtD hv rfl
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, hw]))

/-! ## Output normalization -/

private def scaleOp (op : FOp) (r : Nat) (srcs : List Opnd) (mode : FMode := .ieee) : Op :=
  .float { op := op, ty := ⟨.f32, 1⟩, mode := mode, ftz := true, dsts := [some r], srcs := srcs }

private theorem readScaleReal {t : TState} {r : Nat} {v : Value} {x : ℝ}
    (hr : t.regs r = some v) (hx : valFloat .f32 v = .ok x) :
    Assumption.readERealOpnd t .f32 (.reg r) = some (.ok (x : EReal)) :=
  (readERealOpnd_reg hr).trans (readEReal_of_valFloat hx)

private theorem exec_scaleIdeal {L : Launch} {g : Nat} {t : TState} {op : Op}
    {f : Assumption.FloatForm} (hf : Assumption.FloatForm.ofOp op = some f)
    (hm : f = .setp .f32 ∨ f = .subRn .f32 ∨ f = .add .f32)
    {v : Exec TState} (hv : Assumption.execIdealFloat L g t op = some v) :
    execLocalA asms L g t op = v :=
  Assumption.execLocalA_idealReal hf (by rcases hm with rfl | rfl | rfl <;> decide)
    (fun a ha l i state _ => asms_segment_free (L := l) (g := i) state a
      (List.mem_cons_of_mem _ ha)) hv

private theorem exec_scaleApprox {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hi : Assumptions.idealArith.localRule L g t op = none)
    {v : Exec TState} (ha : Assumptions.approx.localRule L g t op = some v) :
    execLocalA asms L g t op = v := by
  rw [execLocalA_noSegment (asms_segment_free t)]
  unfold execLocalRule
  simp only [Assumptions.all, List.findSome?_cons, hi, ha]

private theorem erealScaleFinite (x : ℝ) :
    Assumption.erealValue .f32 (x : EReal) = fl x := by
  simp [Assumption.erealValue, fl, EReal.coe_ne_bot, EReal.coe_ne_top]

private theorem exec_scaleEmptyTest {L : Launch} {g : Nat} {d : D} {t : TState}
    (hr : t.regs 482 = some (fl d.li)) :
    execLocalA asms L g t
      (scaleOp (.setp (.ord .eq) none) 120 [.reg 482, .f32imm 0]) =
      .ok (PTX.next (setReg t 120 (.pred (decide (d.li = 0))))) := by
  apply exec_scaleIdeal (f := .setp .f32) rfl (by decide)
  have hli := readScaleReal hr (valFloat_float (x := d.li))
  have hz : Assumption.readERealOpnd t .f32 (.f32imm 0) = some (.ok (0 : EReal)) := by
    change Assumption.readEReal .f32 (b32 0) = _
    exact (readEReal_of_valFloat valFloat_z0).trans (by rw [EReal.coe_zero])
  simp only [scaleOp, Assumption.execIdealFloat, Assumption.bindRead, hli, hz,
    Assumption.erealCompare, pure, Except.pure]
  have h : (decide ((d.li : EReal) = (0 : EReal))) = decide (d.li = 0) := by
    by_cases hs : d.li = 0 <;> simp [hs, ← EReal.coe_zero]
  rw [h]

private def scaleExponent (P : Params) (L : Launch) (g : Nat) (d : D) : Value :=
  match P.sink (head L g) with
  | some _ => fl (Result.sinkLog2 P (head L g) - reference d)
  | none => negInf

private def scaleSinkValue (P : Params) (L : Launch) (g : Nat) (d : D) : Value :=
  match P.sink (head L g) with
  | some _ => fl (sinkTerm P L g d)
  | none => fl 0

private theorem exec_scaleSub {d : D} {t : TState} (hs : t.regs 2880 = some (sinkReg P L g))
    (hr : t.regs 481 = some (miVal d)) :
    execLocalA asms L g t (scaleOp .sub 1741 [.reg 2880, .reg 481]) =
      .ok (PTX.next (setReg t 1741 (scaleExponent P L g d))) := by
  apply exec_scaleIdeal (f := .subRn .f32) rfl (by decide)
  have hmi := readScaleReal hr (valFloat_miVal d)
  cases hsink : P.sink (head L g) with
  | none =>
    have hread : Assumption.readERealOpnd t .f32 (.reg 2880) = some (.ok ⊥) := by
      rw [readERealOpnd_reg hs, sinkReg_none hsink]
      rfl
    have hsub : Assumption.addEReal ⊥ (-(reference d : EReal)) = some ⊥ := by
      simp [Assumption.addEReal]
    have hbot : Assumption.erealValue .f32 ⊥ = negInf := by
      simp [Assumption.erealValue]
      rfl
    simp [scaleOp, scaleExponent, hsink, Assumption.execIdealFloat, Assumption.bindRead, hread,
      hmi, hsub, hbot, pure, Except.pure]
  | some s =>
    have hread := readScaleReal (by simpa [sinkReg, hsink] using hs)
      (valFloat_float (x := s * log2e))
    have hsub : Assumption.addEReal ((s * log2e : ℝ) : EReal) (-(reference d : EReal)) =
        some ((s * log2e - reference d : ℝ) : EReal) := by
      rw [← EReal.coe_neg]
      simp [Assumption.addEReal, sub_eq_add_neg]
    simp only [scaleOp, scaleExponent, hsink, Result.sinkLog2, Assumption.execIdealFloat,
      Assumption.bindRead, hread, hmi, hsub, Option.map_some, erealScaleFinite, pure, Except.pure]

private theorem readScaleFinite {t : TState} {r : Nat} {v : Value} {x : ℝ}
    (hr : t.regs r = some v) (hx : valFloat .f32 v = .ok x) :
    Assumption.readFinite t .f32 (.reg r) = some (.ok x) := by
  simp only [Assumption.readFinite, readScaleReal hr hx, Assumption.bindRead, EReal.coe_ne_top,
    EReal.coe_ne_bot, or_self, ↓reduceIte, EReal.toReal_coe, pure, Except.pure]

private theorem exec_scaleEx2 {d : D} {t : TState} (hr : t.regs 1741 = some (scaleExponent P L g d))
    (hpc : t.pc = 1193) :
    execLocalA asms L g t (scaleOp .ex2 1742 [.reg 1741] .approx) =
      .ok (PTX.next (setReg t 1742 (scaleSinkValue P L g d))) := by
  let op := scaleOp .ex2 1742 [.reg 1741] .approx
  change execLocalA asms L g t op = _
  cases hsink : P.sink (head L g) with
  | none =>
    have hneg : t.regs 1741 = some negInf := by simpa [scaleExponent, hsink] using hr
    have hread : Assumption.readERealOpnd t .f32 (.reg 1741) = some (.ok ⊥) := by
      rw [readERealOpnd_reg hneg]
      rfl
    have hnone : ∀ a ∈ asms, a.localRule L g t op = none := by
      intro a ha
      simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | simp [op, scaleOp, Assumptions.approx, Assumption.approxExact,
            Assumption.ApproxForm.ofOp, Assumption.execApproxExact, Assumption.readFinite,
            Assumption.bindRead, hread, Assumptions.paramPointers, Assumptions.sharedBits, hpc,
            Assumptions.deadPackRule, Assumptions.peerPackRule]
    rw [execLocalA_noSegment (asms_segment_free t), execLocalRule_of_none hnone]
    change execFloat L g t
      { op := .ex2
        ty := ⟨.f32, 1⟩
        mode := .approx
        ftz := true
        dsts := [some 1742]
        srcs := [.reg 1741] } = _
    simp [execFloat, readValue, readReg, hneg, pure, Except.pure, bind, Except.bind,
      scaleSinkValue, hsink, show List.range 1 = [0] from rfl]
    rfl
  | some s =>
    have hf : Assumption.readFinite t .f32 (.reg 1741) =
        some (.ok (Result.sinkLog2 P (head L g) - reference d)) := by
      have hv : t.regs 1741 = some (fl (Result.sinkLog2 P (head L g) - reference d)) := by
        simpa [scaleExponent, hsink] using hr
      exact readScaleFinite hv valFloat_float
    apply exec_scaleApprox (op := op) rfl
    simp [op, scaleOp, Assumptions.approx, Assumption.approxExact, Assumption.ApproxForm.ofOp,
      Assumption.execApproxExact, hf, Assumption.bindRead, pure, Except.pure, scaleSinkValue,
      sinkTerm, hsink, fl]

private theorem scaleSinkValue_real (P : Params) (L : Launch) (g : Nat) (d : D) :
    valFloat .f32 (scaleSinkValue P L g d) = .ok (sinkTerm P L g d) := by
  cases hs : P.sink (head L g)
  · simp only [scaleSinkValue, sinkTerm, hs, fl, valFloat_float]
  · simp only [scaleSinkValue, hs, fl, valFloat_float]

private theorem exec_scaleAdd {d : D} {t : TState} (ha : t.regs 482 = some (fl d.li))
    (hb : t.regs 1742 = some (scaleSinkValue P L g d)) :
    execLocalA asms L g t (scaleOp .add 1743 [.reg 482, .reg 1742]) =
      .ok (PTX.next (setReg t 1743 (fl (d.li + sinkTerm P L g d)))) := by
  apply exec_scaleIdeal (f := .add .f32) rfl (by decide)
  have ha' := readScaleReal ha valFloat_float
  have hb' := readScaleReal hb (scaleSinkValue_real P L g d)
  have hadd : Assumption.addEReal (d.li : EReal) (sinkTerm P L g d : EReal) =
      some ((d.li + sinkTerm P L g d : ℝ) : EReal) := by
    simp [Assumption.addEReal]
  simp only [scaleOp, Assumption.execIdealFloat, Assumption.bindRead, ha', hb', hadd,
    Option.map_some, erealScaleFinite, pure, Except.pure]

private theorem exec_scaleDiv {d : D} {t : TState} (h1 : t.regs 1744 = some (b32 1065353216))
    (hdenom : t.regs 1743 = some (fl (d.li + sinkTerm P L g d))) (hrow : RowTotal d)
    (hne : d.li ≠ 0) :
    execLocalA asms L g t (scaleOp .div 2956 [.reg 1744, .reg 1743] .approx) =
      .ok (PTX.next (setReg t 2956 (fl (oScale P L g d)))) := by
  let op := scaleOp .div 2956 [.reg 1744, .reg 1743] .approx
  change execLocalA asms L g t op = _
  have hpos : 0 < d.li := lt_of_le_of_ne hrow.1 (Ne.symm hne)
  have hs : 0 ≤ sinkTerm P L g d := by
    cases hsink : P.sink (head L g)
    · simp [sinkTerm, hsink]
    · simp only [sinkTerm, hsink]
      positivity
  have hne' : d.li + sinkTerm P L g d ≠ 0 := by linarith
  have hOne : f32Value 1065353216 = some 1 := by
    simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
      Layout.magnitude, Layout.bias, Layout.width, FVal.num]
    norm_num
  have hi : valFloat .f32 (b32 1065353216) = .ok 1 := by
    simpa using valFloat_b32 (by decide : 1065353216 < 2 ^ 64) hOne
  have hread1 := readScaleFinite h1 hi
  have hread2 := readScaleFinite hdenom valFloat_float
  apply exec_scaleApprox (op := op) rfl
  simp [op, scaleOp, Assumptions.approx, Assumption.approxExact, Assumption.ApproxForm.ofOp,
    Assumption.execApproxExact, hread1, hread2, Assumption.bindRead, pure, Except.pure, oScale,
    hne, hne', fl]

private def scaleFrame (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  epiFacts P L g d 1187

private def scaleScalar (P : Params) (L : Launch) (g : Nat) (d : D) : Value :=
  if d.li = 0 then b32 0 else fl (oScale P L g d)

private theorem scalePrefix {d : D} {t : TState} (ht : At t 1188 (scaleFrame P L g d)) :
    ∃ u, run kernel asms L g 3 t = some u ∧
      At u 1191 ((120, .pred (decide (d.li = 0))) :: (2956, b32 0) :: scaleFrame P L g d) := by
  let F := scaleFrame P L g d
  obtain ⟨t₁, hrun₁, h₁⟩ : ∃ t₁, run kernel asms L g 1 t = some t₁ ∧ At t₁ 1189 F := by
    simp only [F, scaleFrame, epiFacts] at ht ⊢
    seg_fp ht using skip
  have hli : t₁.regs 482 = some (fl d.li) :=
    holds_mem h₁.2.2.2.2 (mem_factsFrom (r := 482) (by decide +kernel))
  let t₂ := PTX.next (setReg t₁ 120 (.pred (decide (d.li = 0))))
  have hex : execLocalA asms L g t₁
      (scaleOp (.setp (.ord .eq) none) 120 [.reg 482, .f32imm 0]) = .ok t₂ :=
    exec_scaleEmptyTest hli
  have hrun₂ : run kernel asms L g 1 t₁ = some t₂ :=
    run_local Flow.code_1189 rfl h₁ hex
  have h₂ : At t₂ 1190 ((120, .pred (decide (d.li = 0))) :: F) :=
    h₁.set (not_mem_factsFrom (by decide +kernel))
  obtain ⟨u, hrun₃, h₃⟩ : ∃ u, run kernel asms L g 1 t₂ = some u ∧
      At u 1191 ((120, .pred (decide (d.li = 0))) :: (2956, b32 0) :: F) := by
    simp only [F, scaleFrame, epiFacts] at h₂ ⊢
    seg_fp h₂ using norm_bits
  exact ⟨u, run_comp (run_comp hrun₁ hrun₂) hrun₃, h₃⟩

private theorem run_scaleResult {d : D} {t : TState} (hrow : RowTotal d) (hne : d.li ≠ 0)
    (ht : At t 1192 (scaleFrame P L g d)) :
    ∃ u, run kernel asms L g 5 t = some u ∧
      At u 1197 ((2956, scaleScalar P L g d) :: scaleFrame P L g d) := by
  let F := scaleFrame P L g d
  have hp : d.peak ≠ ⊥ := fun h => hne (hrow.2.mpr h)
  have hsink : t.regs 2880 = some (sinkReg P L g) :=
    holds_mem ht.2.2.2.2 (mem_factsFrom (r := 2880) (by decide +kernel))
  have hmi : t.regs 481 = some (miVal d) := by
    have hr := holds_mem ht.2.2.2.2 (mem_factsFrom (r := 481) (by decide +kernel))
    change t.regs 481 = some (lseRefVal d) at hr
    simpa only [lseRefVal, hp, ↓reduceIte] using hr
  let x := scaleExponent P L g d
  let y := scaleSinkValue P L g d
  let z := fl (d.li + sinkTerm P L g d)
  let t₁ := PTX.next (setReg t 1741 x)
  have hrun₁ : run kernel asms L g 1 t = some t₁ :=
    run_local Flow.code_1192 rfl ht (exec_scaleSub hsink hmi)
  have h₁ : At t₁ 1193 ((1741, x) :: F) :=
    ht.set (not_mem_factsFrom (by decide +kernel))
  let t₂ := PTX.next (setReg t₁ 1742 y)
  have hrun₂ : run kernel asms L g 1 t₁ = some t₂ :=
    run_local Flow.code_1193 rfl h₁ (exec_scaleEx2 h₁.2.2.2.2.1 h₁.1)
  have h₂ : At t₂ 1194 ((1742, y) :: F) :=
    (h₁.mono h₁.2.2.2.2.2).set (not_mem_factsFrom (by decide +kernel))
  have hli : t₂.regs 482 = some (fl d.li) :=
    holds_mem h₂.2.2.2.2.2 (mem_factsFrom (r := 482) (by decide +kernel))
  let t₃ := PTX.next (setReg t₂ 1743 z)
  have hrun₃ : run kernel asms L g 1 t₂ = some t₃ :=
    run_local Flow.code_1194 rfl h₂ (exec_scaleAdd hli h₂.2.2.2.2.1)
  have h₃ : At t₃ 1195 ((1743, z) :: F) :=
    (h₂.mono h₂.2.2.2.2.2).set (not_mem_factsFrom (by decide +kernel))
  obtain ⟨t₄, hrun₄, h₄⟩ : ∃ t₄, run kernel asms L g 1 t₃ = some t₄ ∧
      At t₄ 1196 ((1744, b32 1065353216) :: (1743, z) :: F) := by
    simp only [F, scaleFrame, epiFacts] at h₃ ⊢
    seg_fp h₃ using norm_bits
  let t₅ := PTX.next (setReg t₄ 2956 (fl (oScale P L g d)))
  have hrun₅ : run kernel asms L g 1 t₄ = some t₅ :=
    run_local Flow.code_1196 rfl h₄ (exec_scaleDiv h₄.2.2.2.2.1 h₄.2.2.2.2.2.1 hrow hne)
  have h₅ : At t₅ 1197 ((2956, fl (oScale P L g d)) :: F) :=
    (h₄.mono h₄.2.2.2.2.2.2).set (not_mem_factsFrom (by decide +kernel))
  exact ⟨t₅, run_comp (run_comp (run_comp (run_comp hrun₁ hrun₂) hrun₃) hrun₄) hrun₅,
    by simpa only [scaleScalar, hne, ↓reduceIte] using h₅⟩

private theorem scaleTail {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (_hw : warpOf L g < 4)
    {t : TState} (ht : At t 1197 ((2956, scaleScalar P L g d) :: scaleFrame P L g d)) :
    ∃ u, run kernel asms L g 4 t = some u ∧ At u 1201 (epiFacts P L g d 1201) := by
  let F := (2956, scaleScalar P L g d) :: scaleFrame P L g d
  have hr : t.regs 3001 = some (.ptr 64 true (.param (param "1")) 0) :=
    holds_mem ht.2.2.2.2.2 (mem_factsFrom (r := 3001) (by decide +kernel))
  let t₁ := PTX.next (setReg t 3832 (b64 (P.param1Base + 512)))
  have hrun : run kernel asms L g 1 t = some t₁ :=
    run_paramAdd Flow.code_1197 ht (by decide) hr hpre.param1Object (by decide)
  have h₁ : At t₁ 1198 ((3832, b64 (P.param1Base + 512)) :: F) := ht.set (by
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      change (2956 : Nat) ≠ 3832
      decide
    · exact not_mem_factsFrom (by decide +kernel) q hq)
  obtain ⟨u, hrun₂, h₂⟩ : ∃ u, run kernel asms L g 3 t₁ = some u ∧
      At u 1201 (epiFacts P L g d 1201) := by
    simp only [F, scaleFrame, epiFacts] at h₁ ⊢
    by_cases hzero : d.li = 0
    all_goals simp only [scaleScalar, hzero, ↓reduceIte] at h₁
    all_goals seg_fp h₁ using
      try epi_values
      all_goals first
        | exact congrArg Value.pred (warpGtOne _hw)
        | rfl
        | simp [oScaleWord, hzero]
  exact ⟨u, run_comp hrun hrun₂, h₂⟩

private theorem run_epilogueScale {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hrow : RowTotal d)
    (hw : warpOf L g < 4) {t : TState} (ht : At t 1188 (epiFacts P L g d 1187)) :
    ∃ u, Relation.ReflTransGen (Tau kernel asms L g) t u ∧ At u 1201 (epiFacts P L g d 1201) := by
  obtain ⟨t₁, hrun₁, h₁⟩ := scalePrefix ht
  by_cases hzero : d.li = 0
  · have hpred : t₁.regs 120 = some (.pred true) := by
      simpa only [hzero, decide_true] using h₁.2.2.2.2.1
    have hnone (a : Assumption) (ha : a ∈ asms) : a.localRule L g t₁ (.bra 1197 false) = none :=
      Thread.asms_localRule_bra (t := t₁) (by rw [h₁.1]; decide)
        (by rw [h₁.1]; decide) a ha
    obtain ⟨t₂, hrun₂, h₂⟩ := run_bra Flow.code_1191 true h₁ hpred hnone (by seg_free_pc)
    have ht₂ : At t₂ 1197 ((2956, scaleScalar P L g d) :: scaleFrame P L g d) := by
      simpa only [scaleScalar, hzero, ↓reduceIte] using h₂.mono h₂.2.2.2.2.2
    obtain ⟨u, hrun₃, hu⟩ := scaleTail hpre hw ht₂
    exact ⟨u, run_rtg (run_comp (run_comp hrun₁ hrun₂) hrun₃), hu⟩
  · have hpred : t₁.regs 120 = some (.pred false) := by
      simpa only [hzero, decide_false] using h₁.2.2.2.2.1
    have hnone (a : Assumption) (ha : a ∈ asms) : a.localRule L g t₁ (.bra 1197 false) = none :=
      Thread.asms_localRule_bra (t := t₁) (by rw [h₁.1]; decide)
        (by rw [h₁.1]; decide) a ha
    obtain ⟨t₂, hrun₂, h₂⟩ := run_bra Flow.code_1191 false h₁ hpred hnone (by seg_free_pc)
    obtain ⟨t₃, hrun₃, h₃⟩ := run_scaleResult hrow hzero (h₂.mono h₂.2.2.2.2.2.2)
    obtain ⟨u, hrun₄, hu⟩ := scaleTail hpre hw h₃
    exact ⟨u, run_rtg (run_comp (run_comp (run_comp hrun₁ hrun₂) hrun₃) hrun₄), hu⟩
end

/-- The Tensor Memory fence leaves the last-block state, normalizes O and opens the first tile. -/
theorem step_fenceEpilogue {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) (hd : d.site = .fenceEpilogue) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat inv hc hf => by
    have hpc : d.site.pc = 1187 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1187)
    change e = ⟨d.site.pc, .tc .fenceAfter⟩ ∧ some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using inv.subLt
    have hstart := at_next_of hat hpc hsub
    rw [← Option.some.inj hu] at hstart
    have hrow := inv.rowTotal (by rw [hd]; rfl)
    obtain ⟨v, hr, hv⟩ := run_epilogueScale hpre hrow inv.warpLt hstart
    let d' : D := { d with site := .oLoad 0, sub := 0 }
    have hi : Inv P L g d' :=
      epiInv inv (by rw [hd]; rfl) (by rw [hd]; rfl) rfl (by intro h; cases h)
    refine Or.inl (Or.inr ⟨d', v, ?_, hr, ?_, hi⟩)
    · simp [next, nextSite, hd, he, d', hsub]
    · exact epiAtD hv rfl

/-! ## Output event footprints -/

variable {P : Params} {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

private theorem epilogue_firedAt {op : Op} (hc : kernel.code[d.site.pc]? = some ⟨none, op⟩)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ t, (code P L g).AtD d t ∧ Inv P L g d ∧
      Fires d.site.pc (eventTmpl asms L g t op) e (some u) := by
  obtain ⟨t, ht, hf⟩ := h
  change (code P L g).AtD d t ∧ Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hf
  rw [ht.1.1, hc] at hf
  exact ⟨t, ht.1, ht.2, hf⟩

/-- The output load for a tile delivers consecutive words at its Tensor Memory column. -/
theorem fired_outputLoad {j : Fin 4} {mem0 : Mem0} (hpre : Pre P L mem0) (hd : d.site = .oLoad j)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ words, words.length = 64 ∧ e.kind = .tc (.ld (64 * j.val) words .s32x32b) := by
  have hc := outputLoad_code j
  rw [← hd] at hc
  obtain ⟨t, hat, _, hf⟩ := epilogue_firedAt hc h
  rw [event_oLoad hpre hat hd] at hf
  obtain ⟨words, hlen, he, _⟩ := hf
  exact ⟨words, hlen, congrArg Event.kind he⟩

/-- A staging event writes the four-byte pair computed for this vector element. -/
theorem fired_stageOutput {j : Fin 4} {k : Fin 8} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hd : d.site = .oStage j k)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ a, e.kind = .wr a (stagePair P L g d (4 * k.val + d.sub)).toBytes ∧
      a.loc = shLoc L g (stageWrite L g j.val k.val d.sub) ∧ a.size = 4 := by
  have hc := stage_code j k
  rw [← hd] at hc
  obtain ⟨t, hat, hi, hf⟩ := epilogue_firedAt hc h
  rw [event_oStage hpre hg hat hi hd] at hf
  have hs : t.sub = d.sub := hat.2.1
  have he := congrArg Event.kind hf.1
  rw [hs] at he
  exact ⟨_, he, rfl, rfl⟩

/-- The staged tile is published to all four softmax warps. -/
theorem fired_outputBarrier {j : Fin 4} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hd : d.site = .epiBar j) (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    e.kind = .bar 9 (some 128) .sync := by
  have hc := epiBar_code j
  rw [← hd] at hc
  obtain ⟨t, hat, _, hf⟩ := epilogue_firedAt hc h
  rw [event_epiBar hpre hat hd] at hf
  exact congrArg Event.kind hf.1

/-- The issuer's tensor-store event names the logical box and physical shared tile. -/
theorem fired_outputTile {j : Fin 4} {mem0 : Mem0} (hpre : Pre P L mem0) (hd : d.site = .tmaStore j)
    (hq : qOf L g < P.s_q) (he : eOf L g < P.b)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    e.kind = .tensorStore (P.param1Base + 512) (outputSpec P L g j) := by
  have hc := outputTma_code j
  rw [← hd] at hc
  obtain ⟨t, hat, hi, hf⟩ := epilogue_firedAt hc h
  exact fires_tmaOutput hpre hat hd hi.warpLt hq he hf

/-- The closing synchronization is the full CTA's barrier. -/
theorem fired_outputEveryone {mem0 : Mem0} (hpre : Pre P L mem0) (hd : d.site = .everyone)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) : e.kind = .bar 12 none .sync := by
  have hc : kernel.code[d.site.pc]? =
      some ⟨none, .barSyncN (.reg 2425) (.reg 2426) false⟩ := by
    rw [hd]
    exact Flow.code_1835
  obtain ⟨t, hat, _, hf⟩ := epilogue_firedAt hc h
  rw [event_everyone hpre hat hd] at hf
  exact congrArg Event.kind hf.1

/-- The output issuer is elected with a full-warp mask. -/
theorem fired_outputElection {j : Fin 4} (hd : d.site = .elect j)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ i leader, e.kind = .elect (2 ^ 32 - 1) i leader := by
  have hc := election_code j
  rw [← hd] at hc
  obtain ⟨t, hat, _, hf⟩ := epilogue_firedAt hc h
  have hr : t.regs (electionMask j) = some (b32 (2 ^ 32 - 1)) := by
    have hv := reg_value hat (r := electionMask j) (by rw [hd]; fin_cases j <;> decide +kernel)
    fin_cases j <;> exact hv
  have hbits := readBits_b32 (L := L) (g := g) hr (by decide)
  have hm : electMember (2 ^ 32 - 1) (PTX.laneOf L g) := by
    have hl := Nat.mod_lt (g % L.block) (show 0 < 32 by decide)
    refine ⟨hl, ?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hl
  simp only [eventTmpl, warpTmpl_elect, electTmpl, hbits,
    show (BitVec.ofNat 64 (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 from rfl, hm, ↓reduceIte] at hf
  obtain ⟨i, leader, he, _⟩ := hf
  exact ⟨i, leader, congrArg Event.kind he⟩

/-- The output commit closes the issuing thread's bulk group. -/
theorem fired_outputCommit (hd : d.site = .commit)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) : e.kind = .bulkCommit := by
  have hc : kernel.code[d.site.pc]? = some ⟨none, .bulkCommit⟩ := by
    rw [hd]
    exact Flow.code_1832
  obtain ⟨t, _, _, hf⟩ := epilogue_firedAt hc h
  exact congrArg Event.kind (fires_bulkCommit hf)

/-- The fence before a tile's barrier publishes its shared range to the async proxy. -/
theorem fired_stageFence {j : Fin 4} (hd : d.site = .stageFence j)
    (h : (code P L g).toMachine.Fired (some d) e (some u)) :
    e.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  have hc := stageFence_code j
  rw [← hd] at hc
  obtain ⟨t, _, _, hf⟩ := epilogue_firedAt hc h
  exact congrArg Event.kind (fires_fence_proxy hf).1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
