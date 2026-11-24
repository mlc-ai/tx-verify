-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The CLC poll: a failed poll returns to it, a successful one reads the response. -/
theorem step_clcWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_707)
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 1026) (v := .pred ok) h
    (Flow.not_mem_factsFrom (live := Flow.live Site.clcWait.pc) (by table_decide))
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1026 (.pred false))) = some t' ∧
        At t' Site.clcWait.pc (facts L g ⟨.clcWait, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.clcWait, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
    simp [next]
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1026 (.pred true))) = some t' ∧
        At t' Site.clcLoad.pc (facts L g ⟨.clcLoad, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.clcLoad, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
    simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
