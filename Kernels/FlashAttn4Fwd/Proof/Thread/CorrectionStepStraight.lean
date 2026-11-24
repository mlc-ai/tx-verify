-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepBase

@[expose] public section

/-! # The correction warps' straight steps

The named-barrier syncs, the statistics credits (arrivals with a state register that is not
live), the O-free arrivals on the leader, the staged arrival and the proxy fences: each
continues at the next instruction and reaches its successor site with at most a move of a
literal between. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- Stage 0's first barrier generation, then its credit. -/
theorem step_sync0First {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .sync 0 .first)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_4)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  refine step_of_run (d' := ⟨.credit 0, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.sync 0 .first, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨1, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 0's barrier in a trip, then the load of `α`. -/
theorem step_sync0Loop {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .sync 0 .loop)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_6)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  refine step_of_run (d' := ⟨.ldA 0, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.sync 0 .loop, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 1's barrier in a trip, then the load of `α`. -/
theorem step_sync1Loop {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .sync 1 .loop)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_7)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  refine step_of_run (d' := ⟨.ldA 1, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.sync 1 .loop, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 0's last barrier generation, then the load of `l`. -/
theorem step_sync0Last {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .sync 0 .last)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_8)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  refine step_of_run (d' := ⟨.ldL 0, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.sync 0 .last, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 1's last barrier generation, then the load of `l`. -/
theorem step_sync1Last {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .sync 1 .last)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_9)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  refine step_of_run (d' := ⟨.ldL 1, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.sync 1 .last, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 0's first credit, then stage 1's first barrier generation. -/
theorem step_credit0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .credit 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_16)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 4805 ∉ Flow.live Flow.mbarArrive_16 ++ [] by table_decide))
  refine step_of_run (d' := ⟨.sync 1 .first, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.credit 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg h1 hpre

/-- Stage 1's credit in a trip, then stage 1's barrier. -/
theorem step_credit1 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .credit 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_18)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 4935 ∉ Flow.live Flow.mbarArrive_18 ++ [] by table_decide))
  refine step_of_run (d' := ⟨.sync 1 .loop, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.credit 1, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg h1 hpre

/-- Stage 1's credit after the loop, then stage 0's last barrier generation. -/
theorem step_credit3 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .credit 3) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_21)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5066 ∉ Flow.live Flow.mbarArrive_21 ++ [] by table_decide))
  refine step_of_run (d' := ⟨.sync 0 .last, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.credit 3, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg h1 hpre

/-- Stage 0's O-free arrival in a trip, then stage 1's credit. -/
theorem step_oFree0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oFree 0 false)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_17)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  refine step_of_run (d' := ⟨.credit 1, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.oFree 0 false, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 1's O-free arrival in a trip, then stage 0's credit. -/
theorem step_oFree1 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oFree 1 false)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_19)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  refine step_of_run (d' := ⟨.credit 2, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.oFree 1 false, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 0's final O-free arrival, then its staged arrival. -/
theorem step_oFree0Fin {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oFree 0 true)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_23)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  refine step_of_run (d' := ⟨.staged 0, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.oFree 0 true, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 1's final O-free arrival, then its staged arrival. -/
theorem step_oFree1Fin {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oFree 1 true)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_26)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  refine step_of_run (d' := ⟨.staged 1, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.oFree 1 true, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 0's staged arrival, then stage 1's last barrier generation. -/
theorem step_staged0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .staged 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_24)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5197 ∉ Flow.live Flow.mbarArrive_24 ++ [] by table_decide))
  refine step_of_run (d' := ⟨.sync 1 .last, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.staged 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg h1 hpre

/-- Stage 0's proxy fence, then its final O-free arrival. -/
theorem step_fence0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .fence 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
  obtain rfl :=
    fires_next (show AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) from trivial) hf
  refine step_of_run (d' := ⟨.oFree 0 true, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.fence 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

/-- Stage 1's proxy fence, then its final O-free arrival. -/
theorem step_fence1 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .fence 1) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
  obtain rfl :=
    fires_next (show AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) from trivial) hf
  refine step_of_run (d' := ⟨.oFree 1 true, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.fence 1, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
