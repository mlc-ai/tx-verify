-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ArithCore

@[expose] public section

/-! # `mul.f32` without a rounding modifier has an outcome only under the ideal reading

A proof tool, next to `coreFloat_add_error` (`FloatOutcome.lean`). `mul.f32` written without a
rounding modifier has no Core rule (`FloatInstr.arith` needs a written rounding), so where the ideal
reading (ASM-IDEAL) declines (a NaN operand, `0 · ∞`) it faults. An outcome of `mulE` is therefore
the value of the extended-real product of its operands (`mulE_ok`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

theorem coreFloat_mul_error {fz : Bool} (va vb : Value) :
    ∃ e, coreFloat (mulI fz) [va, vb] = .error e := by
  have hl : ∀ xs, FloatInstr.lane (mulI fz) xs = none := fun xs => by
    simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.arith, Option.bind]
  cases hxa : classify .f32 va with
  | error e => exact ⟨e, by simp [coreFloat, floatLane, hxa, bind, Except.bind]⟩
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => exact ⟨e, by simp [coreFloat, floatLane, hxa, hxb, bind, Except.bind]⟩
  | ok xb => exact ⟨.noRule, by simp [coreFloat, floatLane, hxa, hxb, hl, bind, Except.bind,
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw]⟩

/-- **An outcome of `mul.f32` is the value of the product of the operands' extended reals.** -/
theorem mulE_ok {fz : Bool} {va vb v : Value} (h : mulE fz va vb = .ok v) :
    ∃ x y r, readEReal .f32 va = some (.ok x) ∧ readEReal .f32 vb = some (.ok y) ∧
      mulEReal x y = some r ∧ v = erealValue .f32 r := by
  unfold mulE at h
  cases hi : idealMul va vb with
  | none =>
    rw [hi] at h
    obtain ⟨e, he⟩ := coreFloat_mul_error (fz := fz) va vb
    simp only at h
    rw [he] at h
    cases h
  | some r =>
    rw [hi] at h
    simp only at h
    subst h
    unfold idealMul at hi
    rcases hx : readEReal .f32 va with _ | (e | x) <;> rw [hx] at hi <;> simp only [bindRead] at hi
    all_goals try (simp [pure, Except.pure] at hi; done)
    rcases hy : readEReal .f32 vb with _ | (e | y) <;> rw [hy] at hi <;>
      try simp only at hi
    all_goals try (simp [pure, Except.pure] at hi; done)
    rcases hm : mulEReal x y with _ | m <;> rw [hm] at hi <;> simp [pure, Except.pure] at hi
    subst hi
    exact ⟨x, y, m, rfl, rfl, hm, rfl⟩

end

end PTX.Flow
