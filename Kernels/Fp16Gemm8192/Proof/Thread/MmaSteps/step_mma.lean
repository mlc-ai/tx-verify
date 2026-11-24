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

/-- An MMA issue continues at the next instruction; the local code to the slot's next MMA
(or its commit) is evaluated. -/
theorem step_mma {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (s j : Fin 4) (hs : d.site = .mma s j)
    (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ad, bd, en, hc'⟩ := code_mma s j
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  have hu : u = PTX.next t := fires_tcMma (by decide) hf
  subst hu
  have h1 := At.next h
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g (mmaGap s j) (PTX.next t) = some t' ∧
      At t' (mmaNext s j).pc (facts L g ⟨mmaNext s j, w, q, fp, ap, cp, resp, x⟩) := by
    fin_cases s <;> fin_cases j <;> mseg h1 hpre [mmaNext_ne_full]
  exact ⟨⟨mmaNext s j, w, q, fp, ap, cp, resp, x⟩, t', next_mma s j w q fp ap cp resp x L g e,
    run_rtg hr, ht',
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
