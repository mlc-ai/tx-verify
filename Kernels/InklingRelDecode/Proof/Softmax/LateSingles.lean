-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesC
public import Lemmas.Flow.TypedSingleF

@[expose] public section

/-! # `neg.f32` at pc 807 and `lg2.approx.ftz.f32` at pc 2562 on `.f32` data

The two single-instruction readings (`negExact`, `lg2Exact`) write a datum of four bytes whenever
their operand is one: the exact value where the reading applies, Core's rule where it declines
(`negE_total`, `lg2E_total`). The operand needs no further fact, so the strict piece at either pc
only has to know the tag of the operand register (`Dat32`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat}

/-- The exact base-2 logarithm of a positive finite operand (`lg2Exact`); `none` otherwise. -/
def lg2Val (va : Value) : Option (Exec Value) :=
  bindRead (readEReal .f32 va) fun x =>
    if 0 < x ∧ x ≠ ⊤ then some (pure (.float .f32 (Real.logb 2 x.toReal))) else none

/-- **The outcome of `lg2.approx.ftz.f32`** at pc 2562: the exact logarithm, or Core's table. -/
@[irreducible] def lg2E (va : Value) : Exec Value :=
  match lg2Val va with
  | some r => r
  | none => coreFloat (lg2I true) [va]

theorem lg2E_total {va : Value} (ha : Dat32 va) : ∃ v, lg2E va = .ok v ∧ Dat32 v := by
  obtain ⟨c, hc⟩ := ha.1
  unfold lg2E
  rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
  · have hv : lg2Val va = none := by simp [lg2Val, hx, bindRead]
    obtain ⟨b, rfl⟩ := readEReal_none_nan hc hx
    obtain ⟨o, ho⟩ := lg2I_lane (.nan b) (by simp)
    refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
    simp [hv, coreFloat, lg2I, ty1, floatLane, show List.range 1 = [0] from rfl, hc, ho,
      bind, Except.bind, pure, Except.pure]
  · by_cases h0 : 0 < x ∧ x ≠ ⊤
    · have hv : lg2Val va = some (.ok (.float .f32 (Real.logb 2 x.toReal))) := by
        simp [lg2Val, hx, bindRead, h0, pure, Except.pure]
      exact ⟨_, by rw [hv], dat32_float _⟩
    · have hv : lg2Val va = none := by simp [lg2Val, hx, bindRead, h0]
      obtain ⟨o, ho⟩ := lg2I_lane c (lg2_nonpos hc hx h0)
      refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
      simp [hv, coreFloat, lg2I, ty1, floatLane, show List.range 1 = [0] from rfl, hc, ho,
        bind, Except.bind, pure, Except.pure]

/-- The reading at pc 2562: the exact logarithm, or Core's outcome. -/
theorem exec_lg2 {t : TState} (hpc : t.pc = 2562) {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA Assumptions.all L g t (.float { lg2I true with dsts := [some d], srcs := [a] }) =
      (lg2E va).map fun v => PTX.next (setReg t d v) := by
  set op : Op := .float { lg2I true with dsts := [some d], srcs := [a] } with hop
  have hseg : SegFreePc Assumptions.all t.pc := Kernels.InklingRelDecode.Proof.segFree (by
    rw [hpc]; decide +kernel)
  have h1 : Assumptions.idealArith.localRule L g t op = none :=
    idealReal_localRule_none fun f h => by simp [hop, FloatForm.ofOp] at h
  have h2 : Assumptions.approx.localRule L g t op = none :=
    approxExact_localRule_none fun f h => by simp [hop, ApproxForm.ofOp] at h
  have h3 : (Assumptions.swExp2 kernel).localRule L g t op = none := rfl
  have h4 : Assumptions.lg2Exact.localRule L g t op = (lg2Val va).map
      (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [Assumptions.lg2Exact, Assumptions.lg2Sites, hpc, hop, lg2Val, ha.2, bindRead_map]
    simp
    rcases readEReal .f32 va with _ | (e | x)
    · rfl
    · rfl
    · simp only [bindRead]
      split_ifs <;> rfl
  have h5 : Assumptions.divFullExact.localRule L g t op = none := by
    simp [Assumptions.divFullExact, Assumptions.divFullSites, hpc]
  have h6 : Assumptions.negExact.localRule L g t op = none := by
    simp [Assumptions.negExact, Assumptions.negSites, hpc]
  have h7 : Assumptions.bf16Exact.localRule L g t op = none := by
    simp [Assumptions.bf16Exact, hop]
  have h8 : Assumptions.commitOrder.localRule L g t op = none := rfl
  have h9 : Assumptions.pollAgree.localRule L g t op = none := rfl
  have h10 : Assumptions.setMaxNRegSync.localRule L g t op = none := rfl
  have h11 : Assumptions.inputReadOnly.localRule L g t op = none := rfl
  rw [hseg.exec rfl]
  simp only [execLocalRule, Assumptions.all, List.findSome?, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11]
  unfold lg2E
  cases hv : lg2Val va with
  | some r => simp
  | none => simp [hop, execLocal_lg2_core ha]

/-- **The step of `lg2.approx.ftz.f32 d, a` at pc 2562** on a datum writes a datum. -/
theorem lg2_step {t : TState} (hpc : t.pc = 2562) {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) (hd : Dat32 va) :
    ∃ v, execLocalA Assumptions.all L g t
        (.float { lg2I true with dsts := [some d], srcs := [a] }) =
      .ok (PTX.next (setReg t d v)) ∧ Dat32 v := by
  obtain ⟨v, hv, hdv⟩ := lg2E_total hd
  exact ⟨v, by rw [exec_lg2 hpc ha, hv]; rfl, hdv⟩

/-- **The step of `neg.f32 d, a` at pc 807** on a datum writes a datum. -/
theorem neg_step {t : TState} (hpc : t.pc = 807) {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) (hd : Dat32 va) :
    ∃ v, execLocalA Assumptions.all L g t
        (.float { negI false with dsts := [some d], srcs := [a] }) =
      .ok (PTX.next (setReg t d v)) ∧ Dat32 v := by
  obtain ⟨v, hv, hdv⟩ := negE_total (fz := false) hd
  exact ⟨v, by rw [exec_neg hpc ha, hv]; rfl, hdv⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
