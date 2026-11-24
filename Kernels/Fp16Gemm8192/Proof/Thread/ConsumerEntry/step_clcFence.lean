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

/-- The fence reaches the group barrier. -/
theorem step_clcFence {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcFence) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_719)
  obtain rfl := fires_next (show AdvancesOp (.fence (.proxy (.async (some (.shared .cta))))) from
    trivial) hf
  have h1 := At.next h
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 0 (PTX.next t) = some t' ∧
      At t' Site.clcBar.pc (facts L g ⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
    cons_seg h1 hpre
  right
  refine ⟨⟨.clcBar, m, n, m', n', cp, ap, resp, x, acc, base⟩, t', ?_, run_rtg hr, ht',
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hi.7⟩⟩
  simp [next]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
