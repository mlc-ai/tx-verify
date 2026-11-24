-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.Base

@[expose] public section

/-! One step of `LoaderSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- From the instruction after the last block's arrival (taken or skipped), the code
increments the K count and either starts the next trip or ends the task. -/
theorem trip_end {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    (hpre : Pre P L mem0) (hi : Inv d)
    (h : At t ((Site.arrive 7).pc + 1) (factsAt L g ((Site.arrive 7).pc + 1) d)) :
    ∃ k t', run kernel Prod L g k t = some t' ∧
      At t' (endOfTrip d).site.pc (facts L g (endOfTrip d)) ∧ Inv (endOfTrip d) := by
  obtain ⟨s, m, n, q, cp, r, x⟩ := d
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : q < 128 := hi.q
  have hq8 : q % 8 = 0 := hi.q8
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 t = some t1 ∧
      At t1 ((Site.arrive 7).pc + 3) (factsAt L g ((Site.arrive 7).pc + 3) ⟨s, m, n, q + 8, cp, r,
        x⟩) := by
    loader_seg h hpre
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) code_trip
    (decide (q + 8 ≠ 128)) ht1 (holds_mem ht1.2.2.2.2 (trip_branch_fact L g _))
    (prod_localRule_bra L g _ _ _)
  by_cases hlast : q + 8 < 128
  · have hd : decide (q + 8 ≠ 128) = true := by simp; omega
    rw [hd] at ht2
    simp only [↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 4 t2 = some t3 ∧
        At t3 (Site.wait 0).pc (facts L g ⟨.wait 0, m, n, q + 8, cp, r, x⟩) := by
      loader_seg ht2 hpre
    refine ⟨_, t3, run_comp (run_comp hr1 hr2) hr3, ?_, ?_⟩
    · simpa [endOfTrip, hlast] using ht3
    · simp only [endOfTrip, hlast, ↓reduceIte]
      exact ⟨hm, hn, hlast, by show (q + 8) % 8 = 0; omega, hi.cp, hi.x⟩
  · have hd : decide (q + 8 ≠ 128) = false := by simp; omega
    rw [hd] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 t2 = some t3 ∧
        At t3 Site.clcWait.pc (facts L g ⟨.clcWait, m, n, q, cp, r, x⟩) := by
      loader_seg ht2 hpre
    refine ⟨_, t3, run_comp (run_comp hr1 hr2) hr3, ?_, ?_⟩
    · simpa [endOfTrip, hlast] using ht3
    · simp only [endOfTrip, hlast, ↓reduceIte]
      exact ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
