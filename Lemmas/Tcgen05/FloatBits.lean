-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Bits of representable floating payloads

Field magnitudes increase with the field, so a payload whose number is the magnitude of a field up
to `maxField` has exactly that field as its bits (THREAD-BITS): the rounding of EXT-FLOAT-BITS is
exact on representable numbers. -/

namespace PTX.Proof
open PTX

noncomputable section

theorem magnitude_zero (fmt : FloatFmt) : fmt.magnitude 0 = 0 :=
  Layout.magnitude_zero fmt.expBits fmt.mantBits

theorem magnitude_lt_succ (fmt : FloatFmt) (F : Nat) :
    fmt.magnitude F < fmt.magnitude (F + 1) :=
  Layout.magnitude_lt_succ fmt.expBits fmt.mantBits F

theorem magnitude_strictMono (fmt : FloatFmt) : StrictMono fmt.magnitude :=
  Layout.magnitude_strictMono fmt.expBits fmt.mantBits

open Classical in
/-- The bits of a number whose magnitude is the magnitude of a field up to `maxField`: that field
and the sign of the number. -/
private theorem encode_of_abs (fmt : FloatFmt) {F : Nat} (hF : F ≤ fmt.maxField) {x : ℝ}
    (habs : |x| = (fmt.magnitude F : ℝ)) :
    fmt.encode x = (if x < 0 then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F := by
  have hmono : StrictMono fun G => (fmt.magnitude G : ℝ) := by
    intro a b h
    show (fmt.magnitude a : ℝ) < (fmt.magnitude b : ℝ)
    exact_mod_cast magnitude_strictMono fmt h
  rw [FloatFmt.encode_eq]
  rw [habs]
  set lo := Nat.findGreatest (fun G => (fmt.magnitude G : ℝ) ≤ (fmt.magnitude F : ℝ)) fmt.maxField
  have hlo : lo = F := by
    rw [Nat.findGreatest_eq_iff]
    refine ⟨hF, fun _ => le_refl _, fun n hn _ => ?_⟩
    exact not_le.mpr (hmono hn)
  have hnext : (fmt.magnitude F : ℝ) < (fmt.magnitude (F + 1) : ℝ) := hmono (Nat.lt_succ_self F)
  have hmid : ¬ ((((fmt.magnitude F + fmt.magnitude (F + 1)) / 2 : ℚ) : ℝ) <
      (fmt.magnitude F : ℝ) ∨
      ((((fmt.magnitude F + fmt.magnitude (F + 1)) / 2 : ℚ) : ℝ) = (fmt.magnitude F : ℝ) ∧
        F % 2 = 1)) := by
    rw [show (((fmt.magnitude F + fmt.magnitude (F + 1)) / 2 : ℚ) : ℝ) =
      ((fmt.magnitude F : ℝ) + (fmt.magnitude (F + 1) : ℝ)) / 2 by push_cast; ring]
    rintro (h | ⟨h, -⟩) <;> linarith
  rw [hlo]
  simp only [hmid, and_false, ↓reduceIte]

open Classical in
/-- The number of a field up to `maxField`, with a sign, encodes as that field and sign. -/
theorem encode_magnitude (fmt : FloatFmt) {F : Nat} (neg : Bool) (hF : F ≤ fmt.maxField)
    (hneg : neg = true → 0 < F) :
    fmt.encode ((if neg then -1 else 1) * (fmt.magnitude F : ℝ)) =
      (if neg then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F := by
  have hnonneg : (0 : ℝ) ≤ (fmt.magnitude F : ℝ) := by
    rcases Nat.eq_zero_or_pos F with h | h
    · rw [h, magnitude_zero]; norm_num
    · have hlt : (fmt.magnitude 0 : ℚ) < fmt.magnitude F := magnitude_strictMono fmt h
      rw [magnitude_zero] at hlt
      have : (0 : ℝ) < (fmt.magnitude F : ℝ) := by exact_mod_cast hlt
      linarith
  have habs : |(if neg then -1 else 1) * (fmt.magnitude F : ℝ)| = (fmt.magnitude F : ℝ) := by
    rw [abs_mul, abs_of_nonneg hnonneg]
    cases neg <;> simp
  cases neg with
  | false =>
    rw [show (if false then (-1 : ℝ) else 1) * (fmt.magnitude F : ℝ) =
      (fmt.magnitude F : ℝ) by simp] at habs ⊢
    rw [encode_of_abs fmt hF habs]
    simp only [Bool.false_eq_true, ↓reduceIte,
      show ¬ ((fmt.magnitude F : ℝ) < 0) from not_lt.mpr hnonneg]
  | true =>
    have hlt : (0 : ℚ) < fmt.magnitude F := by
      rw [← magnitude_zero fmt]
      exact magnitude_strictMono fmt (hneg rfl)
    have hpos : (0 : ℝ) < (fmt.magnitude F : ℝ) := by exact_mod_cast hlt
    rw [show (if true then (-1 : ℝ) else 1) * (fmt.magnitude F : ℝ) =
      -(fmt.magnitude F : ℝ) by simp] at habs ⊢
    rw [encode_of_abs fmt hF habs]
    simp only [↓reduceIte, show (-(fmt.magnitude F : ℝ) < 0) from by linarith]

end

end PTX.Proof
