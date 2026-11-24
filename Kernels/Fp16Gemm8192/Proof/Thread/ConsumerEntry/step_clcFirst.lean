-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The first-CTA query records the claimed CTA and reaches the fence. -/
theorem step_clcFirst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcFirst) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_718)
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcFirst, m, n, m', n', cp, ap, resp, x, acc, base⟩) h
    (show 969 ∈ Flow.live Site.clcFirst.pc by table_decide) hr
  simp only at hresp
  subst hresp
  obtain ⟨⟨cx, cy, cz⟩, hcf⟩ : ∃ c, r.firstCta = some c := by
    cases hc : r.firstCta with
    | none => simp [clcQueryValue, hc] at hq
    | some c => exact ⟨c, rfl⟩
  simp only [clcQueryValue, hcf, pure, Except.pure] at hq
  cases hq
  have hx : cx.toNat < 2 ^ 32 := cx.isLt
  have h0 : At t Site.clcFirst.pc (Flow.factsFrom ((Flow.live Site.clcFirst.pc).erase 143)
      (valueOf L g ⟨.clcFirst, m, n, m', n', cp, ap, .clc r, x, acc, base⟩)) :=
    At.mono h (Flow.holds_factsFrom_mono (live := Flow.live Site.clcFirst.pc) h.2.2.2.2
      (by table_decide))
  have h1 := At.set (r := 143) (v := b32 cx.toNat) h0 (Flow.not_mem_factsFrom (by table_decide))
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 0
      (PTX.next (setReg t 143 (b32 cx.toNat))) = some t' ∧
      At t' Site.clcFence.pc
        (facts L g ⟨.clcFence, m, n, m', n', cp, ap, .clc r, cx.toNat, acc, base⟩) := by
    cons_seg h1 hpre
  right
  refine ⟨⟨.clcFence, m, n, m', n', cp, ap, .clc r, cx.toNat, acc, base⟩, t', ?_, run_rtg hr',
    ht', ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, hx⟩⟩
  simp [next, hcf]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
