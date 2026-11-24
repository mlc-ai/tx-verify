-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! One step of `MmaSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The accumulator commit: with no claimed CTA the code leaves for the exit; otherwise it
flips the phases and returns to the CLC poll (through the claimed-CTA branch). -/
theorem step_accCommit {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} (hpre : Pre P L mem0) (hs : d.site = .accCommit) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.tcCommit .two 872 0 (some (.reg 45)))) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  have hu : u = PTX.next t := fires_tcCommit hf
  subst hu
  have h1 := At.next h
  have hw : w = 8 ∨ w = 9 := hi.w
  have hap : ap < 2 := hi.ap
  have hcp : cp < 2 := hi.cp
  have hx32 : x < 2 ^ 32 := hi.x
  right
  by_cases hx : x = Loader.none32
  · subst hx
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 5 (PTX.next t) = some t' ∧
        At t' Site.exitArrive.pc
          (facts L g ⟨.exitArrive, w, q, fp, ap, cp, resp, Loader.none32⟩) := by
      rcases hw with rfl | rfl
      all_goals mseg h1 hpre [flip_mma ap hap, flip_mma cp hcp]
    exact ⟨⟨.exitArrive, w, q, fp, ap, cp, resp, Loader.none32⟩, t', by simp [next], run_rtg hr,
      ht', ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  · obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 3 (PTX.next t) = some t1 ∧
        At t1 Flow.bra_615 (factsX L g Flow.bra_615 ⟨.accCommit, w, q, fp, 1 - ap, 1 - cp, resp, x⟩
          [(41, .pred (decide (x = Loader.none32)))]) := by
      mseg h1 hpre [flip_mma ap hap, flip_mma cp hcp]
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g)
      Flow.code_615 (decide (x = Loader.none32)) ht1 (holds_mem ht1.2.2.2.2 List.mem_cons_self)
      (prod_localRule_bra L g _ _ _)
    rw [show decide (x = Loader.none32) = false by simp [hx]] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 4 t2 = some t3 ∧
        At t3 Site.clcWait.pc (facts L g ⟨.clcWait, w, q, fp, 1 - ap, 1 - cp, resp, x⟩) := by
      mseg ht2 hpre
    refine ⟨⟨.clcWait, w, q, fp, 1 - ap, 1 - cp, resp, x⟩, t3, ?_,
      run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3,
      ⟨hi.w, hi.q, hi.q4, hi.fp, show 1 - ap < 2 by omega, show 1 - cp < 2 by omega, hi.x⟩⟩
    simp [next, hx]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
