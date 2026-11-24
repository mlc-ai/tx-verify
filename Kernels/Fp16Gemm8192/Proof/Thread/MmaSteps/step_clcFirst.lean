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

/-- The first-CTA query records the claimed CTA and reaches the fence. -/
theorem step_clcFirst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} (hpre : Pre P L mem0) (hs : d.site = .clcFirst) (hi : Inv d)
    (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc (eventTmpl Prod L g t
      (.clcQuery (.first .x) 852 (.reg 975))) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  obtain ⟨r, v, hr, hq, rfl, rfl⟩ := fires_clcQuery hf
  have hresp := resp_of (d := ⟨.clcFirst, w, q, fp, ap, cp, resp, x⟩) h
    (show 975 ∈ Flow.live Site.clcFirst.pc by table_decide) hr
  simp only at hresp
  subst hresp
  obtain ⟨⟨cx, cy, cz⟩, hc⟩ : ∃ c, r.firstCta = some c := by
    cases hc : r.firstCta with
    | none => simp [clcQueryValue, hc] at hq
    | some c => exact ⟨c, rfl⟩
  simp only [clcQueryValue, hc, pure, Except.pure] at hq
  cases hq
  have hx : cx.toNat < 2 ^ 32 := cx.isLt
  -- the query overwrites the claimed-CTA register: drop its old value, record the new one
  have h0 : At t Site.clcFirst.pc (Flow.factsFrom ((Flow.live Site.clcFirst.pc).erase 852)
      (valueOf L g ⟨.clcFirst, w, q, fp, ap, cp, .clc r, x⟩)) :=
    At.mono h (Flow.holds_factsFrom_mono (live := Flow.live Site.clcFirst.pc) h.2.2.2.2
      (by table_decide))
  have h1 := At.set (r := 852) (v := .bits 32 (BitVec.ofNat 64 cx.toNat)) h0
    (not_mem_factsFrom (by table_decide))
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 0
      (PTX.next (setReg t 852 (.bits 32 (BitVec.ofNat 64 cx.toNat)))) = some t' ∧
      At t' Site.clcFence.pc (facts L g ⟨.clcFence, w, q, fp, ap, cp, .clc r, cx.toNat⟩) := by
    mseg h1 hpre
  right
  refine ⟨⟨.clcFence, w, q, fp, ap, cp, .clc r, cx.toNat⟩, t', ?_, run_rtg hr', ht',
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hx⟩⟩
  simp [next, hc]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
