-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Br

@[expose] public section

/-! # The bridge's float steps

The local steps of `lg2.approx.ftz.f32` (pc 2562) and `fma.rn.f32` (pc 2563) as outcomes
(the zero test `setp.equ.f32` is the epilogue's, after the poll: `Epi.seg_p2_setp`):
`exec_lg2E` (the kernel's `lg2Exact`, then Core's table), and `exec_floatE_fma_at`, the
state-local form of `exec_floatE_fma` (`Lemmas/Flow/FloatOutcome.lean` states it for an
assumption list that has no segment at all, which the kernel's software `exp2` precludes).
The assumptions' readings at the bridge's code: `idealAtBr` and `declineAtBr`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

theorem execLocal_lg2_core {t : TState} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { lg2I with dsts := [some d], srcs := [a] }) =
      (coreFloat lg2I [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { lg2I with dsts := [some d], srcs := [a] } =
      FloatInstr.lane lg2I := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane lg2I [xa] with
  | none => core_float
  | some o => cases o <;> core_float

/-- **The step of `lg2.approx.ftz.f32` at pc 2562** writes the outcome `lg2E` or faults. -/
theorem exec_lg2E {t : TState} (hpc : t.pc = 2562) {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA asms L g t (.float { lg2I with dsts := [some d], srcs := [a] }) =
      (lg2E va).map fun v => PTX.next (setReg t d v) := by
  rw [(segFree (pc := 2562) (by omega)).exec hpc]
  have h1 : Assumptions.idealArith.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none :=
    Assumption.idealReal_localRule_none fun f h => by simp [FloatForm.ofOp] at h
  have h2 : Assumptions.approx.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none :=
    Assumption.approxExact_localRule_none fun f h => by simp [ApproxForm.ofOp] at h
  have h3 : (Assumptions.swExp2 kernel).localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none := rfl
  have h4 : Assumptions.lg2Exact.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) =
      bindRead (readEReal .f32 va) fun x =>
        if 0 < x ∧ x ≠ ⊤ then
          some (pure (next (setReg t d (.float .f32 (Real.logb 2 x.toReal))))) else none := by
    simp only [Assumptions.lg2Exact, hpc, Assumptions.lg2Sites]
    simp [ha.2]
  have h5 : Assumptions.divFullExact.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none := by
    simp [Assumptions.divFullExact, hpc, Assumptions.divFullSites]
  have h6 : Assumptions.negExact.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none := by
    simp [Assumptions.negExact, hpc, Assumptions.negSites]
  have h7 : Assumptions.bf16Exact.localRule L g t
      (.float { lg2I with dsts := [some d], srcs := [a] }) = none := rfl
  simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h2, h3, h4, h5, h6, h7]
  unfold lg2E
  rcases hr : readEReal .f32 va with _ | (e | x)
  · simp only [bindRead]
    exact execLocal_lg2_core ha
  · simp only [bindRead]
    rfl
  · simp only [bindRead]
    split_ifs
    · rfl
    · exact execLocal_lg2_core ha

/-! ### `fma.rn.f32` and `setp.f32` at the bridge's code -/

/-- `fma.f32` and `setp.f32` are exact at the bridge's code after the `lg2` (pc 2563 on). -/
theorem idealAtBr {f : Assumption.FloatForm} (hf : f = .fma .f32 ∨ f = .setp .f32)
    {t : TState} (h : 2563 ≤ t.pc) : Assumption.IdealAt asms f L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact Assumption.idealAt_head (by rcases hf with rfl | rfl <;> decide)
    (segFree (by omega)).tail

/-- At the bridge's code (pc 2563 on) an `fma.f32` or `setp.f32` the ideal rule declines takes
the Core rule. -/
theorem declineAtBr {f : Assumption.FloatForm} (hfs : f = .fma .f32 ∨ f = .setp .f32)
    {t : TState} (h : 2563 ≤ t.pc) : DeclineAt asms f L g t := by
  intro op hf hn
  rw [(segFree (by omega)).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ asms.drop 2
  · refine asms_tail_none h (fun c hc => ?_) a hd
    subst hc
    rcases hfs with rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-- **The step of `fma.rn.f32`** at a state where the ideal rule is in force and its declines
take the Core rule: it writes the outcome `floatE` or faults. -/
theorem exec_floatE_fma_at {t : TState} (hA : IdealAt asms (.fma .f32) L g t)
    (hD : DeclineAt asms (.fma .f32) L g t) {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} {va vb vc : Value}
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hc : OpndIs L g t c vc) :
    execLocalA asms L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (floatE (fmaI rnd fz) [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      some (.fma .f32) := by simp [FloatForm.ofOp]
  have hI : execIdealFloat L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] })
      = (idealVal (fmaI rnd fz) [va, vb, vc]).map
        (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, hc.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (fmaI rnd fz) [va, vb, vc] with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_fma_core ha hb hc]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

end
end PTX.Kernels.InklingRelDecode.Proof.Br
