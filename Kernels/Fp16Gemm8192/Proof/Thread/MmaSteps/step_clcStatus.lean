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

/-- The status query: a cancelling response reaches the first-CTA query, any other the fence. -/
theorem step_clcStatus {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcStatus) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery .isCanceled 1002 (.reg 975))) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcStatus, w, q, fp, ap, cp, resp, x⟩) h
    (show 975 ∈ Flow.live Site.clcStatus.pc by table_decide) hr
  simp only at hresp
  subst hresp
  simp only [clcQueryValue] at hq
  cases hq
  have h1 := At.set (r := 1002) (v := .pred r.firstCta.isSome) h
    (facts_ne (show 1002 ∉ Flow.live Site.clcStatus.pc by table_decide))
  have hix : Inv ⟨.clcFence, w, q, fp, ap, cp, .clc r, Loader.none32⟩ :=
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, by show Loader.none32 < 2 ^ 32; decide⟩
  right
  cases hc : r.firstCta with
  | some c =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3
        (PTX.next (setReg t 1002 (.pred true))) = some t' ∧
        At t' Site.clcFirst.pc (facts L g ⟨.clcFirst, w, q, fp, ap, cp, .clc r, Loader.none32⟩) :=
          by
      mseg h1 hpre
    refine ⟨⟨.clcFirst, w, q, fp, ap, cp, .clc r, Loader.none32⟩, t', ?_, run_rtg hr', ht', ?_⟩
    · simp [next, hc]
    · exact ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, by show Loader.none32 < 2 ^ 32; decide⟩
  | none =>
    rw [hc] at h1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 1002 (.pred false))) = some t' ∧
        At t' Site.clcFence.pc (facts L g ⟨.clcFence, w, q, fp, ap, cp, .clc r, Loader.none32⟩) :=
          by
      mseg h1 hpre
    refine ⟨⟨.clcFence, w, q, fp, ap, cp, .clc r, Loader.none32⟩, t', ?_, run_rtg hr', ht', hix⟩
    simp [next, hc]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
