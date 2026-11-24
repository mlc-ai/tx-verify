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

/-- A poll of slot `s`'s full barrier: a failed poll returns to it, a successful one reaches
the slot's first MMA. -/
theorem step_full {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {base par : Nat} (hpre : Pre P L mem0) (s : Fin 4) (hs : d.site = .full s)
    (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc
      (eventTmpl Prod L g t (.mbarWait (slotPred s) base 0 (.reg par) true .cta)) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := slotPred s) (v := .pred ok) h (facts_ne (slotPred_not_live s))
  right
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t (slotPred s) (.pred false))) = some t' ∧
        At t' (Site.full s).pc (facts L g ⟨.full s, w, q, fp, ap, cp, resp, x⟩) := by
      fin_cases s
      all_goals mseg h1 hpre
    exact ⟨⟨.full s, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t (slotPred s) (.pred true))) = some t' ∧
        At t' (Site.mma s 0).pc (facts L g ⟨.mma s 0, w, q, fp, ap, cp, resp, x⟩) := by
      fin_cases s
      · rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq
          mseg h1 hpre [accumulates]
        · have hq' : q ≠ 0 := by omega
          mseg h1 hpre [accumulates, hq']
      · mseg h1 hpre
      · mseg h1 hpre
      · mseg h1 hpre
    exact ⟨⟨.mma s 0, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
