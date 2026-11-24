-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepSetup
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWorkPre
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepTrip

@[expose] public section

/-! # The end of an item

Stage 1's staged arrival (a state register that is not live) ends item `i`: the parities of
the item flip (`xor.b32 … 1`), the item register advances by the number of clusters, and
`@%p306 bra` returns to the loop's head (`setp.lt.s32 %p298`, then stage 0's first barrier)
while item `i + 1` exists (`Work.lt_T_iff`), else continues at the tail. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Item `i` exists exactly when its index is below the item count. -/
theorem lt_items_iff (hpre : Pre P L mem0) {i : Nat} :
    i < items L g ↔ work L g i < totOf L := by
  rw [Work.totOf_eq' hpre]
  exact Work.lt_T_iff hpre

theorem work_succ (L : Launch) (g i : Nat) : work L g (i + 1) = work L g i + nClusters L := by
  simp only [work]
  ring

theorem nClusters_eq (hpre : Pre P L mem0) : nClusters L = P.clusters := Work.G_eq hpre

/-- Stage 1's staged arrival, then the next item's first barrier or the tail. -/
theorem step_staged1 {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .staged 1) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_27)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5328 ∉ Flow.live Flow.mbarArrive_27 ++ [] by table_decide))
  have hit : i < items L g := hi.item rfl
  have hw := (lt_items_iff hpre).mp hit
  have hwi := (lt_items_iff (g := g) (i := i + 1) hpre)
  rw [work_succ] at hwi
  have htot := Work.totOf_eq' hpre
  have hG := nClusters_eq hpre
  have hsr := hpre.scheduleRange
  have hcp := hpre.clustersPos
  have hn := trips_lt hpre
  have hn1 : 1 ≤ trips L := by
    have := hpre.skPos; have := hpre.skDiv128; rw [trips, skOf_eq hpre]; omega
  obtain ⟨t2, hr2, ht2⟩ : ∃ t2,
      run kernel asms L g 4 (PTX.next (mbarStateDest t (some 5328))) = some t2 ∧
      At t2 Flow.bra_4891 (factsX L g Flow.bra_4891 ⟨.sync 0 .first, i + 1, 0, aw, a, o⟩
        [(306, .pred (decide (i + 1 < items L g)))]) := by
    corr_segx h1 hpre [work_succ, hwi]
  obtain ⟨t3, hr3, ht3⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[Flow.bra_4891]? = _ from Flow.code_4891) (decide (i + 1 < items L g)) ht2
    (holds_mem ht2.2.2.2.2 (mem_factsX (by table_decide) (by simp [valueX])))
    asms_localRule_none
  by_cases hl : i + 1 < items L g
  · simp only [hl, decide_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
        At t4 (Site.sync 0 .first).pc (facts L g ⟨.sync 0 .first, i + 1, 0, aw, a, o⟩) := by
      corr_segx ht3 hpre
    exact step_of_run (d' := ⟨.sync 0 .first, i + 1, 0, aw, a, o⟩)
      (by simp [next, nextItem, hl])
      ⟨fun _ => hl, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun h' => by simp [Site.inTrip] at h', fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t4, run_comp hr2 (run_comp hr3 hr4), ht4⟩
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 0 t3 = some t4 ∧
        At t4 Site.tailWait.pc (facts L g ⟨.tailWait, i + 1, 0, aw, a, o⟩) := by
      corr_segx ht3 hpre
    exact step_of_run (d' := ⟨.tailWait, i + 1, 0, aw, a, o⟩)
      (by simp [next, nextItem, hl])
      ⟨fun h' => by simp [Site.inItem] at h', fun _ _ _ _ => by simp only; omega,
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t4, run_comp hr2 (run_comp hr3 hr4), ht4⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
