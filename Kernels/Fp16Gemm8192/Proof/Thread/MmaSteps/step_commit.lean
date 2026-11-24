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

/-- A commit to slot `s`'s empty barrier: the next slot's poll, or, after the last slot, the
trip's end: the next trip (through the trip-count branch), or the accumulator commit. -/
theorem step_commit {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (s : Fin 4) (hs : d.site = .commit s)
    (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨base, mask, hc'⟩ := code_commit s
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  have hu : u = PTX.next t := fires_tcCommit hf
  subst hu
  have h1 := At.next h
  have hq : q < 128 := hi.q
  have hq4 : q % 4 = 0 := hi.q4
  have hfp : fp < 2 := hi.fp
  right
  fin_cases s
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
        At t' (Site.full 1).pc (facts L g ⟨.full 1, w, q, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.full 1, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
        At t' (Site.full 2).pc (facts L g ⟨.full 2, w, q, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.full 2, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
        At t' (Site.full 3).pc (facts L g ⟨.full 3, w, q, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.full 3, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  · -- the last slot: the flip and the count (the count's predicate is not in the table, so
    -- the facts at the trip-count branch give it), then the branch
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 3 (PTX.next t) = some t1 ∧
        At t1 Flow.bra_609 (factsX L g Flow.bra_609 ⟨.commit 3, w, q + 4, 1 - fp, ap, cp, resp, x⟩
          [(40, .pred (decide (q + 4 ≠ 128)))]) := by
      mseg h1 hpre [flip_mma fp hfp]
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g)
      Flow.code_609 (decide (q + 4 ≠ 128)) ht1 (holds_mem ht1.2.2.2.2 List.mem_cons_self)
      (prod_localRule_bra L g _ _ _)
    have h4 : ¬ (q + 4 = 0) := by omega
    by_cases hl : q + 4 < 128
    · have hd : decide (q + 4 ≠ 128) = true := by simp; omega
      rw [hd] at ht2
      simp only [↓reduceIte] at ht2
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 3 t2 = some t3 ∧
          At t3 (Site.full 0).pc (facts L g ⟨.full 0, w, q + 4, 1 - fp, ap, cp, resp, x⟩) := by
        mseg ht2 hpre [h4]
      refine ⟨⟨.full 0, w, q + 4, 1 - fp, ap, cp, resp, x⟩, t3, ?_,
        run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3, ⟨hi.w, show q + 4 < 128 by omega,
        show (q + 4) % 4 = 0 by omega, show 1 - fp < 2 by omega, hi.ap, hi.cp, hi.x⟩⟩
      simp [next, endOfTrip, hl]
    · have hd : decide (q + 4 ≠ 128) = false := by simp; omega
      rw [hd] at ht2
      simp only [Bool.false_eq_true, ↓reduceIte] at ht2
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 t2 = some t3 ∧
          At t3 Site.accCommit.pc (facts L g ⟨.accCommit, w, q, 1 - fp, ap, cp, resp, x⟩) := by
        mseg ht2 hpre
      refine ⟨⟨.accCommit, w, q, 1 - fp, ap, cp, resp, x⟩, t3, ?_,
        run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3, ⟨hi.w, hi.q, hi.q4,
        show 1 - fp < 2 by omega, hi.ap, hi.cp, hi.x⟩⟩
      simp [next, endOfTrip, hl]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
