-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormalizeIndex
import Kernels.FlashKdaFwd.Audit.OneTokenNormalize

/-! Arithmetic for the one-token normalization. The PTX explicitly rounds the fused square
updates. The ten additions have implicit rounding and the inspected binary uses separate FADDs. -/
namespace FlashKda.Normalize
open PTX OneToken
noncomputable section

def add32 (round : Option FloatRound) : FloatInstr :=
  { op := .add, ty := ⟨.f32,1⟩, rnd := round, ftz := true, dsts := [], srcs := [] }

/-- Register names control routing, while the arithmetic rule depends on the operation and flags. -/
theorem square_route (d s : Nat) (prev : Opnd) (xs : List FVal) :
    (match sumSquare d s prev with
      | ⟨_,.float f⟩ => f.lane xs | _ => none) = square.lane xs := rfl

def laneAt (ins : Option Instr) (xs : List FVal) : Option FOut :=
  match ins with
  | some ⟨_,.float f⟩ => f.lane xs
  | _ => none

theorem add_route (delta input temp predicate result : Nat) (xs : List FVal) :
    laneAt (exchangeAndAdd delta input temp predicate result)[1]? xs =
      (add32 none).lane xs := rfl

/-- The core deliberately omits bare arithmetic when compiler contraction is possible. -/
theorem implicit_add_unspecified (xs : List FVal) : (add32 none).lane xs = none := rfl

abbrev wordValue (bits : Nat) := Layout.fieldVal 8 23 bits false

/-- A proposed binary32 field witnesses an exact positive normal result, or positive zero. -/
def exactField (v : FVal) (bits : Nat) : Bool :=
  v == wordValue bits && (bits == 0 ||
    (bits ≤ binary32.topField && binary32.minNormal ≤ Layout.magnitude 8 23 bits))

theorem exactField_sound {v bits} (h : exactField v bits = true) :
    FloatFmt.f32.layout.roundVal .rn true v = some (wordValue bits) := by
  simp only [exactField, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨rfl, h⟩ := h
  rcases h with rfl | h
  · rfl
  by_cases zero : bits = 0
  · subst bits; rfl
  have pos := Layout.magnitude_pos (eb := 8) (mb := 23) (Nat.pos_of_ne_zero zero)
  have large : binary32.minNormal ≤ Layout.magnitude 8 23 bits := by simpa using h.2
  have positive : (0:ℝ) < (Layout.magnitude 8 23 bits : ℚ) := by exact_mod_cast pos
  have enough : ¬ |((Layout.magnitude 8 23 bits : ℚ) : ℝ)| < (binary32.minNormal : ℚ) := by
    rw [abs_of_pos positive]
    exact_mod_cast not_lt.mpr large
  change binary32.roundVal .rn true _ = _
  simp only [wordValue, Layout.fieldVal, zero, ↓reduceIte, Bool.false_eq_true]
  simp only [Layout.roundVal]
  unfold Layout.roundFtz
  rw [Layout.round_exact (m := .rn) (F := bits) (by trivial) (Nat.pos_of_ne_zero zero)
    (by simpa using h.1) (abs_of_pos positive) (by simp)]
  simp [enough, Layout.fieldVal, zero, Layout.flush, Layout.subnormal, abs_of_pos pos,
    not_lt.mpr large, not_lt.mpr positive.le]

def squareStep (acc x : FVal) : Option FVal := do
  let .val y ← square.lane [x,x,acc] | none
  return y

/-- Check both the input flush and the exact intermediate before applying the floating rule. -/
def squareCertificate (acc x : FVal) (w : Nat) : Bool :=
  square.flushIn [x,x,acc] == [x,x,acc] && exactField ((x.mul x).add .rn acc) w

theorem squareStep_sound {acc x w} (h : squareCertificate acc x w = true) :
    squareStep acc x = some (wordValue w) := by
  simp only [squareCertificate, Bool.and_eq_true, beq_iff_eq] at h
  have step : square.lane [x,x,acc] = some (.val (wordValue w)) := by
    change (FOut.val <$> square.arith _) = _
    simp [FloatInstr.arith, square, FloatRound.mode]
    have flush := h.1
    unfold square at flush
    rw [flush]
    change FloatFmt.f32.layout.roundVal .rn true _ = _
    exact exactField_sound h.2
  simp [squareStep, step]

def sumStep (a b : FVal) : Option FVal := do
  let .val y ← (add32 (some .rn)).lane [a,b] | none
  return y

theorem sum_of_round {a b v : FVal}
    (inputs : (add32 (some .rn)).flushIn [a,b] = [a,b])
    (result : FloatFmt.f32.layout.roundVal .rn true (a.add .rn b) = some v) :
    sumStep a b = some v := by
  have step : (add32 (some .rn)).lane [a,b] = some (.val v) := by
    change (FOut.val <$> (add32 (some .rn)).arith _) = _
    simp [FloatInstr.arith, add32, FloatRound.mode]
    unfold add32 at inputs
    rw [inputs]
    exact result
  simp [sumStep, step]

end
end FlashKda.Normalize
