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

/-- The status query: a cancelling response reaches the first-CTA query, any other the fence. -/
theorem step_clcStatus {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .clcStatus) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    entry_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_714)
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcStatus, m, n, m', n', cp, ap, resp, x, acc, base⟩) h
    (show 969 ∈ Flow.live Site.clcStatus.pc by table_decide) hr
  simp only at hresp
  subst hresp
  simp only [clcQueryValue] at hq
  cases hq
  have h1 := At.set (r := 1027) (v := .pred r.firstCta.isSome) h
    (Flow.not_mem_factsFrom (live := Flow.live Site.clcStatus.pc) (by table_decide))
  have hix : Inv ⟨.clcFirst, m, n, m', n', cp, ap, .clc r, Loader.none32, acc, base⟩ :=
    ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6, by show Loader.none32 < 2 ^ 32; decide⟩
  cases hc : r.firstCta with
  | some c =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3
        (PTX.next (setReg t 1027 (.pred true))) = some t' ∧
        At t' Site.clcFirst.pc
          (facts L g ⟨.clcFirst, m, n, m', n', cp, ap, .clc r, Loader.none32, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.clcFirst, m, n, m', n', cp, ap, .clc r, Loader.none32, acc, base⟩, t', ?_,
      run_rtg hr', ht', hix⟩
    simp [next, hc]
  | none =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 1027 (.pred false))) = some t' ∧
        At t' Site.clcFence.pc
          (facts L g ⟨.clcFence, m, n, m', n', cp, ap, .clc r, Loader.none32, acc, base⟩) := by
      cons_seg h1 hpre
    right
    refine ⟨⟨.clcFence, m, n, m', n', cp, ap, .clc r, Loader.none32, acc, base⟩, t', ?_,
      run_rtg hr', ht', ⟨hix.1, hix.2, hix.3, hix.4, hix.5, hix.6, hix.7⟩⟩
    simp [next, hc]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
