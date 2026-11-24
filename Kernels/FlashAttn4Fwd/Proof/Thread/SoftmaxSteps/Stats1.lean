-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.SumTail
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Sum0a
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Sum0b

@[expose] public section

/-! # The second statistics poll of an item

A failed poll returns to the poll. After a successful one the first tile's row sum (`lsum0V`,
`Sum0*`) ends with the toggle of the score parity and the branch on `n ≤ 1`: with one tile the
thread leaves to the store of `l`, else it enters the first loop trip. The row sum continues
when it accepts the probabilities (`SumOk0`); otherwise the thread is dead. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The end of the row sum, to the branch on `n ≤ 1` (`s'` the branch's successor). -/
theorem sum0_d (hpre : Pre P L mem0) (i : Nat) (s : Nat → Value) (m l : Value) (s' : Site)
    (hs' : s' = .lSt ∨ s' = .sW true) :
    Seg kernel asms L g 1 2706
      (factsAt L g 2706 ⟨.statsW 1, i, 0, s, m, lsum0V L ⟨.statsW 1, i, 0, s, m, l⟩⟩) 2707
      (factsAt L g 2707 ⟨s', i, 0, s, m, lsum0V L ⟨.statsW 1, i, 0, s, m, l⟩⟩) := by
  intro t h
  rcases hs' with rfl | rfl <;>
    sm_segs h hpre [xor_par, tileIdx_statsW1, tileIdx_sW, tileIdx_lSt]

/-- To the first loop trip's counter. -/
theorem sum0_e (hpre : Pre P L mem0) (i : Nat) (s : Nat → Value) (m l : Value) :
    Seg kernel asms L g 1 2708 (factsAt L g 2707 ⟨.sW true, i, 0, s, m, l⟩) 2709
      (factsAt L g 2709 ⟨.sW true, i, 0, s, m, l⟩) := by
  intro t h
  sm_seg h hpre

/-- **The second statistics poll of an item.** -/
theorem step_statsW1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .statsW 1) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, i, tt, s, m, l⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hw8 := hi.warp
  have hit := hi.item rfl
  obtain rfl : tt = 0 := hi.tile0 rfl
  rw [facts_eq rfl] at h
  rw [← h.1] at hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_32)
  obtain ⟨m', parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 5568) (v := .pred ok) h
    (facts_ne (pc := Flow.mbarWait_32) (by table_decide))
  cases ok with
  | false =>
    refine step_of_run (d' := ⟨.statsW 1, i, 0, s, m, l⟩) (by simp [next]) hi rfl rfl ⟨2, ?_⟩
    sm_seg h1 hpre
  | true =>
    let d0 : D := ⟨.statsW 1, i, 0, s, m, l⟩
    have hA : SegD kernel asms L g (1 + 129) 2575 ((5568, .pred true) :: factsAt L g 2574 d0)
        2706 (factsAt L g 2706 ⟨.statsW 1, i, 0, s, m, lsum0V L d0⟩) (SumOk0 L g d0) :=
      SegD.seg_comp (sum0_a (g := g) hpre i 0 s m l) (sum0_b d0)
    have hn1 := trips_pos hpre
    by_cases hT : trips L ≤ 1
    · let d' : D := ⟨.lSt, i, 0, s, m, lsum0V L d0⟩
      have hB := Seg.bra (K := kernel) (A := asms) (L := L) (g := g)
        (pick := decide (trips L ≤ 1)) (F := factsAt L g 2707 d') Flow.code_2707
        (List.mem_map.mpr ⟨278, by table_decide, by
          simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
        (fun _ _ => asms_localRule_none)
      rw [ite_eq_left_of_eq_true _ _ (by simp [hT])] at hB
      exact step_of_segD (d' := d') (C := SumOk0 L g d0)
        (fun hC => by
          have h' : StatsOk L g 1 d0 := statsOk_1.mpr hC
          simp [d', d0, next, afterStats, hT, h'])
        (fun hC => by
          have h' : ¬ StatsOk L g 1 d0 := mt statsOk_1.mp hC
          simp [d0, next, h'])
        ⟨hw8, fun _ => hit, fun h => by simp [d'] at h, fun h => by simp [d'] at h,
          fun h => by simp [d', Site.tile0] at h, fun h => by simp [d', Site.inTrip] at h,
          fun _ => by simp only [d']; omega, lsum0V_bytes L d0⟩ rfl rfl
        (SegD.comp_seg hA (Seg.comp (sum0_d hpre i s m l .lSt (.inl rfl))
          (Seg.comp hB (Seg.subAt (by table_decide) (lSt_entry hpre hw8 i 0 s m _))))) h1
    · let d' : D := ⟨.sW true, i, 0, s, m, lsum0V L d0⟩
      have hB := Seg.bra (K := kernel) (A := asms) (L := L) (g := g)
        (pick := decide (trips L ≤ 1)) (F := factsAt L g 2707 d') Flow.code_2707
        (List.mem_map.mpr ⟨278, by table_decide, by
          simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
        (fun _ _ => asms_localRule_none)
      rw [ite_eq_right_of_eq_false _ _ (by simp [hT])] at hB
      exact step_of_segD (d' := d') (C := SumOk0 L g d0)
        (fun hC => by
          have h' : StatsOk L g 1 d0 := statsOk_1.mpr hC
          simp [d', d0, next, afterStats, hT, h'])
        (fun hC => by
          have h' : ¬ StatsOk L g 1 d0 := mt statsOk_1.mp hC
          simp [d0, next, h'])
        ⟨hw8, fun _ => hit, fun h => by simp [d'] at h, fun h => by simp [d'] at h,
          fun h => by simp [d', Site.tile0] at h, fun _ => by simp only [d']; omega,
          fun h => by simp [d'] at h, lsum0V_bytes L d0⟩ rfl rfl
        (SegD.comp_seg hA (Seg.comp (sum0_d hpre i s m l (.sW true) (.inr rfl))
          (Seg.comp hB (Seg.comp (sum0_e hpre i s m _) (loop_entry hpre hw8 i 0 s m _))))) h1

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
