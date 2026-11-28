-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatH

@[expose] public section

/-! # `min.f32` of two `.f32` data is a single piece

The outcome of `min.f32` is a datum (`minE_total`) built as a number, a bit pattern or an opaque
NaN, never a packed pair: a store of it writes four bytes of one value (`Simple`). -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Flow.MinCore

noncomputable section

/-- A value that is not a pair or a slice of other values. -/
def Simple (v : Value) : Prop :=
  (∃ w x, v = .bits w x) ∨ (∃ f x, v = .float f x) ∨ ∃ f, v = .nan f

theorem simple_toValue (c : FVal) (f : FloatFmt) : Simple (c.toValue f) := by
  rcases c with neg | q | neg | p
  · cases neg <;> simp [FVal.toValue, Simple]
  · simp [FVal.toValue, Simple]
  · cases neg <;> simp [FVal.toValue, Simple]
  · cases p <;> simp [FVal.toValue, Simple]

theorem simple_erealValue (r : EReal) (f : FloatFmt) : Simple (erealValue f r) := by
  unfold erealValue
  split_ifs
  · exact simple_toValue _ _
  · exact simple_toValue _ _
  · exact .inr (.inl ⟨_, _, rfl⟩)

/-- **The minimum of two `.f32` data is a datum of one piece.** -/
theorem minE_simple {a b : Value} (ha : Dat32 a) (hb : Dat32 b) :
    ∃ v, minE [a, b] = .ok v ∧ Dat32 v ∧ Simple v := by
  have hcore : idealMin [a, b] = none → ∃ v, minE [a, b] = .ok v ∧ Dat32 v ∧ Simple v := by
    intro hn
    obtain ⟨xs, hxs, hl⟩ := mapM_classify (vs := [a, b]) (by simp [ha.1, hb.1])
    obtain ⟨o, ho⟩ := minI_lane xs (by simp [hl])
    refine ⟨o.toValue .f32, ?_, dat32_toValue o, simple_toValue _ _⟩
    unfold minE
    rw [hn]
    simp [coreFloat, minI, ty1, floatLane, show List.range 1 = [0] from rfl, hxs, ho, bind,
      Except.bind, pure, Except.pure]
  rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
  · exact hcore (by simp [idealMin, hx, bindRead])
  rcases readEReal_dat hb.1 with hy | ⟨y, hy⟩
  · exact hcore (by simp [idealMin, hx, hy, bindRead])
  refine ⟨erealValue .f32 (min x y), ?_, dat32_erealValue _, simple_erealValue _ _⟩
  unfold minE
  simp [idealMin, hx, hy, bindRead, pure, Except.pure]

end
end PTX.Flow.TyG
