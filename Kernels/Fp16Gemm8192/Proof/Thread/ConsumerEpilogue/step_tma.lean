-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base

@[expose] public section

/-! One step of `ConsumerEpilogue`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_tma {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {k : Fin 8}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .tma k)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := epi_tma_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_async_next hadv hf
  have hx : x < 2 ^ 32 := hi.x
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1 (PTX.next t) = some t1 ∧
      At t1 (Site.commit k).pc (facts L g ⟨.commit k, m, n, m', n', cp, ap, resp, x, acc, base⟩) :=
        by
    fin_cases k <;> cons_seg (At.next h) hpre
      [epi_setp_bounded (tidOf L g / 32 % 4 ||| tidOf L g % 32) (epi_lead_lt L g),
        epi_setp_none x hx]
  right
  refine ⟨⟨.commit k, m, n, m', n', cp, ap, resp, x, acc, base⟩, t1, by simp [next],
    run_rtg hr1, ht1, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
