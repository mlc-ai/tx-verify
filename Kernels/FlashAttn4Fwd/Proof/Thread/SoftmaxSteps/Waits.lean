-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxBase

@[expose] public section

/-! # The softmax warps' polls

Each poll (`try_wait` in a spin loop: `@P1 bra.uni DONE; bra.uni LAB_WAIT`) writes its result
predicate: a failed poll returns to the poll; a successful poll of the score barrier reaches the
tile's first load, the first statistics poll of an item reaches the score poll, the tail's
reaches the end barrier. (The successful second and loop-end statistics polls run the row-sum
trees, `SoftmaxSteps/Stats*`.) -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- A failed score poll returns to the poll; a successful one reaches the tile's first load. -/
theorem step_sW {ins : Instr} (hpre : Pre P L mem0) (lp : Bool) (hs : d.site = .sW lp)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  rw [facts_eq rfl] at h
  rw [← h.1] at hf
  cases lp
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_31)
    obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
    have h1 := At.set (r := 5471) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_31) (by table_decide))
    cases ok with
    | false =>
      refine step_of_run (d' := ⟨.sW false, i, tt, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
      sm_seg h1 hpre
    | true =>
      refine step_of_run (d' := ⟨.ld false 0, i, tt, s, m, l⟩) (by simp [next])
        (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
        ⟨1, ?_⟩
      sm_seg h1 hpre
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_33)
    obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
    have h1 := At.set (r := 5569) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_33) (by table_decide))
    cases ok with
    | false =>
      refine step_of_run (d' := ⟨.sW true, i, tt, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
      sm_seg h1 hpre
    | true =>
      refine step_of_run (d' := ⟨.ld true 0, i, tt, s, m, l⟩) (by simp [next])
        (inv_move hi rfl rfl rfl rfl (by simp [Site.tile0]) (fun _ => rfl) (by simp)) rfl rfl
        ⟨1, ?_⟩
      sm_seg h1 hpre

/-- The first statistics poll of an item: again, or the score poll. -/
theorem step_statsW0 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .statsW 0) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  rw [facts_eq rfl] at h
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_30)
  obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5470) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_30) (by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.statsW 0, i, tt, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
    sm_seg h1 hpre
  | true =>
    refine step_of_run (d' := ⟨.sW false, i, tt, s, m, l⟩) (by simp [next, afterStats, statsOk_0])
      (inv_move hi rfl rfl rfl rfl (fun _ => rfl) (by simp [Site.inTrip]) (by simp)) rfl rfl
      ⟨2, ?_⟩
    sm_seg h1 hpre

/-- The tail's statistics poll: again, or the end barrier. -/
theorem step_statsW3 {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .statsW 3) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  rw [facts_eq rfl] at h
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_35)
  obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5667) (v := .pred ok) h
      (facts_ne (pc := Flow.mbarWait_35) (by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.statsW 3, i, tt, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
    sm_seg h1 hpre
  | true =>
    have ht := hi.tail (.inl rfl)
    refine step_of_run (d' := ⟨.barEnd, i, tt, s, m, l⟩) (by simp [next, afterStats, statsOk_3])
      ⟨hi.warp, fun h => by simp [Site.inItem] at h, fun _ => ht, fun h => by simp at h,
        fun h => by simp [Site.tile0] at h, fun h => by simp [Site.inTrip] at h,
        fun h => by simp at h, hi.lBytes⟩ rfl rfl ⟨1, ?_⟩
    sm_seg h1 hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
