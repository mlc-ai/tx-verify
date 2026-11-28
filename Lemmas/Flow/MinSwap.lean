-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MinCore
public import Lemmas.Flow.MaxSwap

@[expose] public section

/-! # `min.f32` of two sources does not depend on their order

A proof tool. The outcome of `min.f32` on two sources (`MinCore.minE`) is the minimum of the two
numbers where both read in the extended reals, and the Core rule's `minMax` where one is a NaN.
Both are symmetric, so swapping the sources gives the same value or a fault in both orders
(`minE_comm`), even for NaN operands. -/

namespace PTX.Flow.MinCore
open PTX PTX.Proof PTX.Assumption

noncomputable section

theorem minI_lane (x y : FVal) :
    FloatInstr.lane minI [x, y] = some (.val (FVal.minMax false false x y)) := by
  simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.flushIn, minMaxOp]

theorem coreFloat_min2 (a b : Value) :
    coreFloat minI [a, b] = (do
      let x ← classify .f32 a
      let y ← classify .f32 b
      pure ((FVal.minMax false false x y).toValue .f32)) := by
  simp only [coreFloat, show List.range 1 = [0] from rfl, List.mapM_cons, List.mapM_nil,
    floatLane, bind, Except.bind, pure, Except.pure, ite_true]
  cases classify .f32 a <;> cases classify .f32 b <;>
    simp [minI_lane]

theorem minMax_nan_comm {x y : FVal} (h : x.isNaN = true ∨ y.isNaN = true) :
    FVal.minMax false false x y = FVal.minMax false false y x := by
  rcases hx : x.isNaN <;> rcases hy : y.isNaN <;> simp_all [FVal.minMax]

theorem isNaN_of_read {a : Value} {x : FVal} (h : readEReal .f32 a = none)
    (hc : classify .f32 a = .ok x) : x.isNaN = true := by
  unfold readEReal at h
  split at h
  · split_ifs at h
    rw [hc] at h
    cases x <;> simp_all [FVal.isNaN, readEReal.ofDatum]
  · rw [hc] at h
    cases x <;> simp_all [FVal.isNaN, readEReal.ofDatum]

theorem coreFloat_min2_comm (a b : Value) (h : readEReal .f32 a = none ∨ readEReal .f32 b = none) :
    SameOk (coreFloat minI [a, b]) (coreFloat minI [b, a]) := by
  intro v
  rw [coreFloat_min2, coreFloat_min2]
  rcases ha : classify .f32 a with e | x <;> rcases hb : classify .f32 b with e' | y <;>
    simp only [bind, Except.bind, pure, Except.pure]
  case ok.ok =>
    have nan : x.isNaN = true ∨ y.isNaN = true := by
      rcases h with h | h
      · exact .inl (isNaN_of_read h ha)
      · exact .inr (isNaN_of_read h hb)
    rw [minMax_nan_comm nan]
  all_goals simp

theorem coreFloat_min2_error_a {a b : Value} {e : Fault} (h : classify .f32 a = .error e) :
    ∀ v, coreFloat minI [a, b] ≠ .ok v := by
  intro v
  rw [coreFloat_min2]
  simp [h, bind, Except.bind]

theorem coreFloat_min2_error_b {a b : Value} {e : Fault} (h : classify .f32 b = .error e) :
    ∀ v, coreFloat minI [a, b] ≠ .ok v := by
  intro v
  rw [coreFloat_min2]
  rcases classify .f32 a with e | x <;> simp [h, bind, Except.bind]

/-- **`min.f32 d, a, b` does not depend on the order of `a` and `b`**: the same value, or a fault
in both orders. -/
theorem minE_comm (a b : Value) : SameOk (minE [a, b]) (minE [b, a]) := by
  intro v
  unfold minE idealMin
  rcases ha : readEReal .f32 a with _ | (ea | x) <;>
    rcases hb : readEReal .f32 b with _ | (eb | y) <;> simp only [bindRead, ha, hb]
  all_goals first
    | exact coreFloat_min2_comm a b (.inl ha) v
    | exact coreFloat_min2_comm a b (.inr hb) v
    | simp only [pure, Except.pure, min_comm _ _]
    | (have := coreFloat_min2_error_b (a := a) (readEReal_error_classify hb) v
       simp [this])
    | (have h2 := coreFloat_min2_error_b (a := b) (readEReal_error_classify ha) v
       simp [h2])

end
end PTX.Flow.MinCore
