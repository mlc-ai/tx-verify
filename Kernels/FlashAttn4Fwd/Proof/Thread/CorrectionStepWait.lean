-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll

@[expose] public section

/-! # The correction warps' polls and store waits

Each poll (`try_wait` in a spin loop: `@P1 bra.uni DONE; bra.uni LAB_WAIT`) writes its result
predicate: a failed poll returns to the poll, a successful one leaves the loop. The rescale's
`tcgen05.wait::st` continues at the O-free arrival (`mov.b32 …, 1` between). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}

/-- The poll of the final accumulator of stage 0: again, or the poll of its staging buffer. -/
theorem step_oWait0 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oWait 0)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_36)
  obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5668) (v := .pred ok) h
    (not_mem_factsFrom (show 5668 ∉ Flow.live Flow.mbarWait_36 ++ [] by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.oWait 0, i, tt, aw, a, o⟩) (by simp [next]) hi rfl ⟨2, ?_⟩
    corr_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.fWait 0, i, tt, aw, a, o⟩) (by simp [next])
      (inv_same (d := ⟨.oWait 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip])
        (by simp [Site.rescale]) (by simp)) rfl ⟨1, ?_⟩
    corr_seg h1 hpre

/-- The poll of the staging buffer of stage 0: again, or the first final load (the pair of `1 / l'`
is packed between). -/
theorem step_fWait0 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .fWait 0)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_37)
  obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5669) (v := .pred ok) h
    (not_mem_factsFrom (show 5669 ∉ Flow.live Flow.mbarWait_37 ++ [] by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.fWait 0, i, tt, aw, a, o⟩) (by simp [next]) hi rfl ⟨2, ?_⟩
    corr_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.fld 0 0, i, tt, aw, a, o⟩) (by simp [next])
      (inv_same (d := ⟨.fWait 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip])
        (by simp [Site.rescale]) (by simp)) rfl ⟨2, ?_⟩
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 (PTX.next (setReg t 5669 (.pred true)))
        = some t1 ∧ At t1 4307 (factsAt L g 4307 ⟨.fld 0 0, i, tt, aw, a, o⟩) := by
      corr_seg h1 hpre
    obtain ⟨t2, hr2, ht2⟩ := seg_packRecip (d := ⟨.fld 0 0, i, tt, aw, a, o⟩)
      (liveT := Flow.live (Site.fld 0 0).pc ++ (Site.fld 0 0).extra) Flow.code_4307
      (by decide) (by simp [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])
      (by table_decide) (by simp [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])
      (by decide +kernel) t1 ht1
    exact ⟨t2, run_comp hr1 hr2, ht2⟩

/-- The poll of the final accumulator of stage 1: again, or the poll of its staging buffer. -/
theorem step_oWait1 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .oWait 1)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_38)
  obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5670) (v := .pred ok) h
    (not_mem_factsFrom (show 5670 ∉ Flow.live Flow.mbarWait_38 ++ [] by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.oWait 1, i, tt, aw, a, o⟩) (by simp [next]) hi rfl ⟨2, ?_⟩
    corr_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.fWait 1, i, tt, aw, a, o⟩) (by simp [next])
      (inv_same (d := ⟨.oWait 1, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip])
        (by simp [Site.rescale]) (by simp)) rfl ⟨1, ?_⟩
    corr_seg h1 hpre

/-- The poll of the staging buffer of stage 1: again, or the first final load. -/
theorem step_fWait1 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .fWait 1)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_39)
  obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5671) (v := .pred ok) h
    (not_mem_factsFrom (show 5671 ∉ Flow.live Flow.mbarWait_39 ++ [] by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.fWait 1, i, tt, aw, a, o⟩) (by simp [next]) hi rfl ⟨2, ?_⟩
    corr_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.fld 1 0, i, tt, aw, a, o⟩) (by simp [next])
      (inv_same (d := ⟨.fWait 1, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip])
        (by simp [Site.rescale]) (by simp)) rfl ⟨2, ?_⟩
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 (PTX.next (setReg t 5671 (.pred true)))
        = some t1 ∧ At t1 4603 (factsAt L g 4603 ⟨.fld 1 0, i, tt, aw, a, o⟩) := by
      corr_seg h1 hpre
    obtain ⟨t2, hr2, ht2⟩ := seg_packRecip (d := ⟨.fld 1 0, i, tt, aw, a, o⟩)
      (liveT := Flow.live (Site.fld 1 0).pc ++ (Site.fld 1 0).extra) Flow.code_4603
      (by decide) (by simp [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])
      (by table_decide) (by simp [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])
      (by decide +kernel) t1 ht1
    exact ⟨t2, run_comp hr1 hr2, ht2⟩

/-- The poll of the last staging buffer: again, or the end barrier. -/
theorem step_tailWait {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .tailWait)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_40)
  obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5672) (v := .pred ok) h
    (not_mem_factsFrom (show 5672 ∉ Flow.live Flow.mbarWait_40 ++ [] by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.tailWait, i, tt, aw, a, o⟩) (by simp [next]) hi rfl ⟨2, ?_⟩
    corr_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.barEnd, i, tt, aw, a, o⟩) (by simp [next])
      (inv_same (d := ⟨.tailWait, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inr (.inl (hi.tail rfl (by simp) (by simp) (by simp)))) (by simp [Site.inTrip])
        (by simp [Site.rescale]) (by simp)) rfl ⟨1, ?_⟩
    corr_seg h1 hpre

/-- The wait for the rescale stores of stage 0, then its O-free arrival. -/
theorem step_rwait0 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .rwait 0)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
  obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
  refine step_of_run (d' := ⟨.oFree 0 false, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.rwait 0, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨1, ?_⟩
  corr_seg (At.next h) hpre

/-- The wait for the rescale stores of stage 1, then its O-free arrival. -/
theorem step_rwait1 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .rwait 1)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_5)
  obtain ⟨rfl, -⟩ := fires_tcWaitSt hf
  refine step_of_run (d' := ⟨.oFree 1 false, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.rwait 1, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
      (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
      (by simp)) rfl ⟨1, ?_⟩
  corr_seg (At.next h) hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
