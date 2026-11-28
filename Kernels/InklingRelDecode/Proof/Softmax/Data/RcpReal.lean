-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.RcpCore
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # The reciprocal of a number other than zero is a number

`rcp.approx.f32` on an operand that reads as an extended real other than zero gives the exact
reciprocal of a finite one, and Core's signed zero for an infinite one: a number either way. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

/-- A zero reads as a number. -/
theorem sk_fl_zero (b : Bool) : SK.fl.Has ((FVal.zero b).toValue .f32) := by
  cases b
  · exact ⟨clean_float 0, 0, readEReal_float 0⟩
  · have e : (FVal.zero true).toValue .f32 = .bits 32 (BitVec.ofNat 64 0x80000000) := rfl
    rw [e]
    have hz : classify .f32 (.bits 32 (BitVec.ofNat 64 0x80000000)) = .ok (.zero true) :=
      classify_bits (fmt := .f32) (n := 0x80000000) (x := .zero true) (by decide)
        (by decide)
    have hc : Clean (.bits 32 (BitVec.ofNat 64 0x80000000)) := by
      refine ⟨rfl, ?_, ?_⟩
      · intro _ _ _ h; cases h
      · intro _ _ h; cases h; decide
    refine ⟨hc, 0, ?_⟩
    change readEReal.ofDatum (classify .f32 (.bits 32 (BitVec.ofNat 64 0x80000000))) = _
    rw [hz]
    rfl

private theorem rcp_inf_lane (fz n : Bool) :
    ∃ b, FloatInstr.lane (rcpI fz) [.inf n] = some (.val (.zero b)) := by
  cases n <;> cases fz <;> first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩

private theorem classify_inf {va : Value} {x : EReal} (hx : readEReal .f32 va = some (.ok x))
    (h : x = ⊤ ∨ x = ⊥) : ∃ n, classify .f32 va = .ok (.inf n) := by
  have h' : readEReal.ofDatum (classify .f32 va) = some (.ok x) := by
    cases va with
    | float f r =>
      by_cases hf : f = .f32
      · subst hf
        simp only [readEReal, ↓reduceIte, pure, Except.pure, Option.some.injEq,
          Except.ok.injEq] at hx
        subst hx
        rcases h with h | h <;> simp at h
      · simpa [readEReal, hf] using hx
    | _ => simpa [readEReal] using hx
  revert h'
  rcases hc : classify .f32 va with e | c
  · simp [readEReal.ofDatum]
  · cases c <;> simp [readEReal.ofDatum, pure, Except.pure]
    all_goals (rcases h with rfl | rfl <;> simp)

/-- **The reciprocal of a number other than zero** is a number. -/
theorem rcpE_real (fz : Bool) {va : Value} {x : EReal}
    (hx : readEReal .f32 va = some (.ok x)) (h0 : x ≠ 0) :
    ∃ v, rcpE fz va = .ok v ∧ SK.fl.Has v := by
  by_cases hb : x = ⊤ ∨ x = ⊥
  · obtain ⟨n, hn⟩ := classify_inf hx hb
    obtain ⟨b, hb'⟩ := rcp_inf_lane fz n
    have hv : rcpVal va = none := by
      simp [rcpVal, finiteVal, hx, hb, bindRead]
    refine ⟨(FVal.zero b).toValue .f32, ?_, sk_fl_zero b⟩
    unfold rcpE
    rw [hv]
    simp [coreFloat, rcpI, ty1, floatLane, show List.range 1 = [0] from rfl, hn, hb', bind,
      Except.bind, pure, Except.pure]
  · have hz : x.toReal ≠ 0 := fun h => by
      rcases EReal.toReal_eq_zero_iff.mp h with h | h | h
      exacts [h0 h, hb (.inl h), hb (.inr h)]
    have hv : rcpVal va = some (pure (.float .f32 (1 / x.toReal))) := by
      simp [rcpVal, finiteVal, hx, hb, bindRead, pure, Except.pure, hz]
    refine ⟨.float .f32 (1 / x.toReal), ?_, clean_float _, _, readEReal_float _⟩
    unfold rcpE
    rw [hv]
    rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
