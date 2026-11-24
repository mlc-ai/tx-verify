-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.SumTail
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Sum1a
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Sum1b
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Sum1c

@[expose] public section

/-! # The statistics poll that ends a loop trip

A failed poll returns to the poll. After a successful one the loop tile's row sum (`lsum1V`,
`Sum1*`) ends with the toggles of the parities, the trip counter, the new reference maximum
(`mNV`) and the loop's branch: the next trip when `t + 2 < n`, else the store of `l`. The row
sum and the move continue when they accept their operands (`SumOk1`); otherwise the thread is
dead. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- **The statistics poll that ends a loop trip.** -/
theorem step_statsW2 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .statsW 2) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  have hit := hi.item rfl
  have htr : tt + 1 < trips L := hi.trip rfl
  rw [facts_eq rfl] at h
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_34)
  obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5666) (v := .pred ok) h
    (facts_ne (pc := Flow.mbarWait_34) (by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.statsW 2, i, tt, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
    sm_seg h1 hpre
  | true =>
    let d0 : D := ⟨.statsW 2, i, tt, s, m, l⟩
    have hA : SegD kernel asms L g (1 + 133) 3588 ((5666, .pred true) :: factsAt L g 3587 d0)
        3723 (factsAt L g 3723 ⟨.statsW 2, i, tt, s, m, lsum1V L d0⟩)
        (oCond (valueOf L g d0) sum1Items) :=
      SegD.seg_comp (sum1_a (g := g) hpre i tt s m l) (sum1_b d0)
    by_cases hT : tt + 2 < trips L
    · let d' : D := ⟨.sW true, i, tt + 1, s, mNV L d0, lsum1V L d0⟩
      have hB := Seg.bra (K := kernel) (A := asms) (L := L) (g := g)
        (pick := decide (tt + 2 < trips L))
        (F := factsX L g 3728 d' [(286, .pred (decide (tt + 2 < trips L)))]) Flow.code_3728
        (List.mem_map.mpr ⟨286, by table_decide, by simp [valueX]⟩)
        (fun _ _ => asms_localRule_none)
      rw [ite_eq_left_of_eq_true _ _ (by simp [hT])] at hB
      have hM := sum1_d (L := L) (g := g) d0 (.sW true) i (tt + 1) s (lsum1V L d0)
        (.pred (decide (tt + 2 < trips L)))
      exact step_of_segD (d' := d') (C := SumOk1 L g d0)
        (fun hC => by
          have h' : StatsOk L g 2 d0 := statsOk_2.mpr hC
          simp [d', d0, next, afterStats, hT, h'])
        (fun hC => by
          have h' : ¬ StatsOk L g 2 d0 := mt statsOk_2.mp hC
          simp [d0, next, h'])
        ⟨hw8, fun _ => hit, fun h => by simp [d'] at h, fun h => by simp [d'] at h,
          fun h => by simp [d', Site.tile0] at h, fun _ => by simp only [d']; omega,
          fun h => by simp [d'] at h, lsum1V_bytes L d0⟩ rfl rfl
        ((SegD.comp hA (SegD.seg_comp
          (sum1_c hpre i tt s m l (mNV L d0) (lsum1V L d0) htr _ (.inr rfl))
          (SegD.comp_seg hM (Seg.comp hB (Seg.sub (ks := [286]) (by decide +kernel)
          (loop_entry hpre hw8 i (tt + 1) s _ _)))))).iff Iff.rfl) h1
    · let d' : D := ⟨.lSt, i, tt + 1, s, mNV L d0, lsum1V L d0⟩
      have hB := Seg.bra (K := kernel) (A := asms) (L := L) (g := g)
        (pick := decide (tt + 2 < trips L))
        (F := factsX L g 3728 d' [(286, .pred (decide (tt + 2 < trips L)))]) Flow.code_3728
        (List.mem_map.mpr ⟨286, by table_decide, by simp [valueX]⟩)
        (fun _ _ => asms_localRule_none)
      rw [ite_eq_right_of_eq_false _ _ (by simp [hT])] at hB
      have hM := sum1_d (L := L) (g := g) d0 (.lSt) i (tt + 1) s (lsum1V L d0)
        (.pred (decide (tt + 2 < trips L)))
      exact step_of_segD (d' := d') (C := SumOk1 L g d0)
        (fun hC => by
          have h' : StatsOk L g 2 d0 := statsOk_2.mpr hC
          simp [d', d0, next, afterStats, hT, h'])
        (fun hC => by
          have h' : ¬ StatsOk L g 2 d0 := mt statsOk_2.mp hC
          simp [d0, next, h'])
        ⟨hw8, fun _ => hit, fun h => by simp [d'] at h, fun h => by simp [d'] at h,
          fun h => by simp [d', Site.tile0] at h, fun h => by simp [d', Site.inTrip] at h,
          fun _ => by simp only [d']; omega, lsum1V_bytes L d0⟩ rfl rfl
        ((SegD.comp hA (SegD.seg_comp
          (sum1_c hpre i tt s m l (mNV L d0) (lsum1V L d0) htr _ (.inl rfl))
          (SegD.comp_seg hM (Seg.comp hB (Seg.sub (ks := [286]) (by decide +kernel)
          (lSt_entry hpre hw8 i (tt + 1) s _ _)))))).iff Iff.rfl) h1

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
