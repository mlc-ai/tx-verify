-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreBase

@[expose] public section

/-! # The store warp's steps inside an item

The polls of the staged barriers (a failed poll returns to it, a successful one reaches the
stage's first TMA store), the TMA stores, the bulk-group commits and waits and the arrival
freeing stage 0. Each continues at the next instruction; the segments to the next site are
moves of literals and the stage-1 row (`or.b32 … 256`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem inv_keep {L : Launch} {g : Nat} {d : D} (s : Site) (hi : Inv L g d)
    (hd : d.site ≠ .exit) : Inv L g ⟨s, d.i⟩ := fun _ => hi hd

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- A poll of stage `st`'s staged barrier. -/
theorem step_wait {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (hs : d.site = .wait st)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  rw [← h.1] at hf
  right
  rcases fin2_cases st with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_28)
    obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
    have h1 := At.set (r := 5468) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_28) (by table_decide))
    cases ok with
    | false =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
          run kernel asms L g 2 (PTX.next (setReg t 5468 (.pred false))) =
          some t' ∧ At t' (Site.wait 0).pc (facts L g ⟨.wait 0, i⟩) := by
        store_seg h1 hpre
      exact ⟨⟨.wait 0, i⟩, t', by simp [next], run_rtg hr, ht', hi⟩
    | true =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
          run kernel asms L g 4 (PTX.next (setReg t 5468 (.pred true))) =
          some t' ∧ At t' (Site.tma 0 0).pc (facts L g ⟨.tma 0 0, i⟩) := by
        store_seg h1 hpre
      exact ⟨⟨.tma 0 0, i⟩, t', by simp [next], run_rtg hr, ht',
        inv_keep _ hi (by simp)⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_29)
    obtain ⟨m, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
    have h1 := At.set (r := 5469) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_29) (by table_decide))
    cases ok with
    | false =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
          run kernel asms L g 2 (PTX.next (setReg t 5469 (.pred false))) =
          some t' ∧ At t' (Site.wait 1).pc (facts L g ⟨.wait 1, i⟩) := by
        store_seg h1 hpre
      exact ⟨⟨.wait 1, i⟩, t', by simp [next], run_rtg hr, ht', hi⟩
    | true =>
      obtain ⟨t', hr, ht'⟩ : ∃ t',
          run kernel asms L g 2 (PTX.next (setReg t 5469 (.pred true))) =
          some t' ∧ At t' (Site.tma 1 0).pc (facts L g ⟨.tma 1 0, i⟩) := by
        store_seg h1 hpre
      exact ⟨⟨.tma 1 0, i⟩, t', by simp [next], run_rtg hr, ht',
        inv_keep _ hi (by simp)⟩

/-- A step whose event continues at `u` and whose segment from `u` reaches `d'`. -/
theorem step_of_run {L : Launch} {g : Nat} {d d' : D} {e : Event}
    {u : TState} (hn : next L g d e = some (some d')) (hi : Inv L g d')
    (hr : ∃ k t', run kernel asms L g k u = some t' ∧ At t' d'.site.pc (facts L g d')) :
    Step asms L g d e u := by
  obtain ⟨k, t', hr, ht'⟩ := hr
  exact .inr ⟨d', t', hn, run_rtg hr, ht', hi⟩

/-- A TMA store of stage `st`, half `hh`: the next half, or the stage's commit. -/
theorem step_tma {ins : Instr} (hpre : Pre P L mem0) (st hh : Fin 2) (hs : d.site = .tma st hh)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hiv : ∀ s, Inv L g ⟨s, i⟩ :=
    fun s => inv_keep (d := ⟨.tma st hh, i⟩) s hi (by simp)
  rcases fin2_cases st with rfl | rfl <;> rcases fin2_cases hh with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_10)
    obtain ⟨rfl, a, sp, hk⟩ := fires_tensorStore hf
    exact step_of_run (d' := ⟨.tma 0 1, i⟩) (by simp [next, hk]) (hiv _)
      ⟨1, by store_seg (At.next h) hpre⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_11)
    obtain ⟨rfl, a, sp, hk⟩ := fires_tensorStore hf
    exact step_of_run (d' := ⟨.commit 0, i⟩) (by simp [next, hk]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_12)
    obtain ⟨rfl, a, sp, hk⟩ := fires_tensorStore hf
    exact step_of_run (d' := ⟨.tma 1 1, i⟩) (by simp [next, hk]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_13)
    obtain ⟨rfl, a, sp, hk⟩ := fires_tensorStore hf
    exact step_of_run (d' := ⟨.commit 1, i⟩) (by simp [next, hk]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩

/-- The commit of stage `st`: the poll of stage 1, or the first bulk wait. -/
theorem step_commit {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (hs : d.site = .commit st)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hiv : ∀ s, Inv L g ⟨s, i⟩ :=
    fun s => inv_keep (d := ⟨.commit st, i⟩) s hi (by simp)
  rcases fin2_cases st with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCommit_0)
    obtain ⟨rfl, rfl⟩ := fires_bulkCommit' hf
    exact step_of_run (d' := ⟨.wait 1, i⟩) (by simp [next]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCommit_1)
    obtain ⟨rfl, rfl⟩ := fires_bulkCommit' hf
    exact step_of_run (d' := ⟨.drain 0, i⟩) (by simp [next]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩

/-- The bulk waits: `read 1` before freeing stage 0, `read 0` before freeing stage 1. -/
theorem step_drain {ins : Instr} (hpre : Pre P L mem0) (r : Fin 2) (hs : d.site = .drain r)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hiv : ∀ s, Inv L g ⟨s, i⟩ :=
    fun s => inv_keep (d := ⟨.drain r, i⟩) s hi (by simp)
  rcases fin2_cases r with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_0)
    obtain ⟨rfl, rfl⟩ := fires_bulkWait hf
    exact step_of_run (d' := ⟨.free 0, i⟩) (by simp [next]) (hiv _)
      ⟨1, by store_seg (At.next h) hpre⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_1)
    obtain ⟨rfl, rfl⟩ := fires_bulkWait hf
    exact step_of_run (d' := ⟨.free 1, i⟩) (by simp [next]) (hiv _)
      ⟨0, by store_seg (At.next h) hpre⟩

/-- The arrival freeing stage 0 (its state register is not live), then the last bulk wait. -/
theorem step_free0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .free 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
  obtain ⟨rfl, m, tx, c, rel, sc, hk, -⟩ := fires_arrive_state hf
  have h1 := At.clear h (facts_ne (pc := Flow.mbarArrive_8) (r := 4101) (by table_decide))
  exact step_of_run (d' := ⟨.drain 1, i⟩) (by simp [next, hk]) (inv_keep _ hi (by simp))
    ⟨0, by store_seg h1 hpre⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store
