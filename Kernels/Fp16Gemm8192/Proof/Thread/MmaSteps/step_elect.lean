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

/-- The election: the leader lane computes the descriptors and reaches the CLC poll; the other
lanes leave for the exit. -/
theorem step_elect {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .elect)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, w, q, fp, ap, cp, resp, x⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_3)
  obtain ⟨mk, inst, leader, rfl, rfl⟩ := fires_elect hf
  have hw : w = 8 ∨ w = 9 := hi.w
  have h1 := At.set (r := 1000) (v := .pred (laneOf L g == leader)) h
    (facts_ne (show 1000 ∉ Flow.live Site.elect.pc by table_decide))
  right
  cases hb : (laneOf L g == leader)
  · -- not the leader: the guarded move is skipped, the test branches to the exit
    rw [hb] at h1
    have hne : ¬ laneOf L g = leader := by simpa using hb
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4
        (PTX.next (setReg t 1000 (.pred false))) = some t' ∧
        At t' Site.exitArrive.pc (facts L g ⟨.exitArrive, w, q, fp, ap, cp, resp, x⟩) := by
      rcases hw with rfl | rfl
      all_goals mseg h1 hpre
    refine ⟨⟨.exitArrive, w, q, fp, ap, cp, resp, x⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.w, hi.q, hi.q4, hi.fp, hi.ap, hi.cp, hi.x⟩⟩
    simp [next, hne]
  · -- the leader: the descriptors of the MMA operands, then the CLC poll. The values depend on
    -- the warp (`w`) and on the shared base (`L.sharedBase = 1024 * k`, `k < 32`): both are
    -- split, and each fact is then closed by evaluation.
    rw [hb] at h1
    have heq : laneOf L g = leader := by simpa using hb
    have hal := hpre.sharedAlignment
    have hbase := hpre.sharedRange
    unfold sharedBytes at hbase
    obtain ⟨k, hk, hsb⟩ : ∃ k, k < 32 ∧ L.sharedBase = 1024 * k :=
      ⟨L.sharedBase / 1024, by omega, by omega⟩
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 34
        (PTX.next (setReg t 1000 (.pred true))) = some t' ∧
        At t' Site.clcWait.pc (facts L g ⟨.clcWait, w, 0, 0, 1, 0, resp, x⟩) := by
      rcases hw with rfl | rfl
      all_goals
        seg_fp h1 using
          try mma_values
          try simp only [hsb, aDesc, bBase, descC]
          all_goals first
            | table_decide
            | (interval_cases k <;> table_decide)
    refine ⟨⟨.clcWait, w, 0, 0, 1, 0, resp, x⟩, t', ?_, run_rtg hr, ht',
      ⟨hi.w, show 0 < 128 by decide, show 0 % 4 = 0 by decide, show 0 < 2 by decide,
        show 1 < 2 by decide, show 0 < 2 by decide, hi.x⟩⟩
    simp [next, heq]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
