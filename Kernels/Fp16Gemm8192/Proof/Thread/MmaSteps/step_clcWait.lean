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

/-- A poll of the CLC barrier: a failed poll returns to it, a successful one reaches the
response read. -/
theorem step_clcWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {base par : Nat} (hpre : Pre P L mem0) (hs : d.site = .clcWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc
      (eventTmpl Prod L g t (.mbarWait 1001 base 0 (.reg par) true .cta)) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 1001) (v := .pred ok) h
    (facts_ne (show 1001 ∉ Flow.live Site.clcWait.pc by table_decide))
  right
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1001 (.pred false))) = some t' ∧
        At t' Site.clcWait.pc (facts L g ⟨.clcWait, w, q, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.clcWait, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1001 (.pred true))) = some t' ∧
        At t' Site.clcLoad.pc (facts L g ⟨.clcLoad, w, q, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.clcLoad, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
