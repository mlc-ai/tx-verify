-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The MMA steps whose local segments are short: the accumulator poll, the acknowledgement and the
exit. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- A poll of slot `s`'s accumulator-empty barrier: a failed poll returns to it; a successful
one reaches the first slot, with the accumulator's first trip (`q = 0`). -/
theorem step_accWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {base par : Nat} (hpre : Pre P L mem0) (hs : d.site = .accWait) (hi : Inv d)
    (hq0 : d.q = 0) (h : At t d.site.pc (facts L g d))
    (hf : Fires d.site.pc
      (eventTmpl Prod L g t (.mbarWait 1005 base 0 (.reg par) true .cta)) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi hq0 ⊢
  subst hs
  subst hq0
  rw [← h.1] at hf
  obtain ⟨mb, parity, ok, sc, rfl, rfl⟩ := fires_wait hf
  have h1 := At.set (r := 1005) (v := .pred ok) h
    (facts_ne (show 1005 ∉ Flow.live Site.accWait.pc by table_decide))
  right
  cases ok with
  | false =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 2
        (PTX.next (setReg t 1005 (.pred false))) = some t' ∧
        At t' Site.accWait.pc (facts L g ⟨.accWait, w, 0, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.accWait, w, 0, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  | true =>
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 5
        (PTX.next (setReg t 1005 (.pred true))) = some t' ∧
        At t' (Site.full 0).pc (facts L g ⟨.full 0, w, 0, fp, ap, cp, resp, x⟩) := by
      mseg h1 hpre
    exact ⟨⟨.full 0, w, 0, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

/-- The acknowledgement's arrival reaches the accumulator poll. -/
theorem step_ack {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ack) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hadv : AdvancesOp ins.op)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hf hi ⊢
  subst hs
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 0 (PTX.next t) = some t' ∧
      At t' Site.accWait.pc (facts L g ⟨.accWait, w, q, fp, ap, cp, resp, x⟩) := by
    mseg h1 hpre
  exact ⟨⟨.accWait, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

/-- The cluster arrival of the exit. -/
theorem step_exitArrive {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exitArrive) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  refine ⟨⟨.exitWait, w, q, fp, ap, cp, resp, x⟩, PTX.next t, by simp [next], .refl, ?_,
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
  exact At.mono (At.next h) (Flow.holds_factsFrom_mono (live := Flow.live Site.exitArrive.pc)
    (live' := Flow.live Site.exitWait.pc) h.2.2.2.2 (by table_decide))

/-- The cluster wait of the exit, then the branch past warp 0's deallocation. -/
theorem step_exitWait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .exitWait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1 (PTX.next t) = some t' ∧
      At t' Site.exit.pc (facts L g ⟨.exit, w, q, fp, ap, cp, resp, x⟩) := by
    mseg (At.next h) hpre
  exact ⟨⟨.exit, w, q, fp, ap, cp, resp, x⟩, t', by simp [next], run_rtg hr, ht',
    ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
