-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Powers of two with real exponents

A proof tool for kernels that exponentiate in base 2 (`Real.rpow 2`, the exact reading of
`ex2.approx` and of software `exp2` segments): sums and differences of exponents
(`two_rpow_add`, `two_rpow_sub`, `two_rpow_sub_sub`), positivity (`two_rpow_pos`,
`sum_two_rpow_pos`), and comparison with one (`two_rpow_lt_one_iff`, `two_rpow_eq_one_iff`). -/

namespace PTX.Numeric

open Finset

theorem two_rpow_pos (a : ℝ) : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos two_pos a

theorem two_rpow_ne_zero (a : ℝ) : (2 : ℝ) ^ a ≠ 0 := (two_rpow_pos a).ne'

theorem two_rpow_zero : (2 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero 2

theorem two_rpow_add (a b : ℝ) : (2 : ℝ) ^ (a + b) = 2 ^ a * 2 ^ b :=
  Real.rpow_add two_pos a b

theorem two_rpow_sub (a b : ℝ) : (2 : ℝ) ^ (a - b) = 2 ^ a / 2 ^ b :=
  Real.rpow_sub two_pos a b

theorem two_rpow_neg (a : ℝ) : (2 : ℝ) ^ (-a) = (2 ^ a)⁻¹ :=
  Real.rpow_neg zero_le_two a

/-- `2 ^ (a - b) = 2 ^ a · 2 ^ (-b)`: a reference exponent factors out. -/
theorem two_rpow_sub_eq_mul (a b : ℝ) : (2 : ℝ) ^ (a - b) = 2 ^ a * 2 ^ (-b) := by
  rw [sub_eq_add_neg, two_rpow_add]

/-- A rescale: `2 ^ (c - c') · 2 ^ (x - c) = 2 ^ (x - c')`. -/
theorem two_rpow_sub_sub (x c c' : ℝ) :
    (2 : ℝ) ^ (c - c') * 2 ^ (x - c) = 2 ^ (x - c') := by
  rw [← two_rpow_add]
  congr 1
  ring

theorem two_rpow_lt_iff {a b : ℝ} : (2 : ℝ) ^ a < 2 ^ b ↔ a < b :=
  Real.rpow_lt_rpow_left_iff one_lt_two

theorem two_rpow_le_iff {a b : ℝ} : (2 : ℝ) ^ a ≤ 2 ^ b ↔ a ≤ b :=
  Real.rpow_le_rpow_left_iff one_lt_two

theorem two_rpow_lt_one_iff {a : ℝ} : (2 : ℝ) ^ a < 1 ↔ a < 0 := by
  rw [← two_rpow_zero, two_rpow_lt_iff]

theorem two_rpow_eq_one_iff {a : ℝ} : (2 : ℝ) ^ a = 1 ↔ a = 0 := by
  constructor
  · intro h
    rw [← two_rpow_zero] at h
    exact le_antisymm (two_rpow_le_iff.mp h.le) (two_rpow_le_iff.mp h.ge)
  · rintro rfl
    exact two_rpow_zero

/-- A nonempty sum of powers of two is positive. -/
theorem sum_two_rpow_pos {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (y : ι → ℝ) :
    0 < ∑ i ∈ s, (2 : ℝ) ^ y i :=
  Finset.sum_pos (fun i _ => two_rpow_pos (y i)) hs

end PTX.Numeric
