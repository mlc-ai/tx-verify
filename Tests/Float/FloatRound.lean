-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Round
public import Mathlib.Tactic.NormNum

/-! The rounding function of THREAD-FLOAT-ROUND and the layouts of THREAD-FLOAT-FORMAT (design §14
item 2). `Layout.round` is noncomputable, so each instance is computed through a characterization
lemma: `Layout.round_exact`, `Layout.round_between`, the overflow lemmas and the fixed-point
lemmas. The binary layouts are those of `.f32`, `.f16`, `.bf16` and `.e4m3`
(`FloatFmt.layout`), and `.s2f6` is `.fixed 8 6`. -/
namespace PTX.Tests.FloatRound
noncomputable section

-- f32: a value of the layout is exact
example : (Layout.binary 8 23 true .ieee).round .rn .inf (1) false =
    some (.fin 1) := by
  rw [Layout.round_exact (m := .rn) (F := 0x3f800000) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: the midpoint above 1 goes to the even code 1
example : (Layout.binary 8 23 true .ieee).round .rn .inf (1 + (2 : ℝ) ^ (-24 : ℤ)) false =
    some (.fin 1) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: the midpoint above the odd code goes up to the even code
example : (Layout.binary 8 23 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-24 : ℤ)) false =
    some (.fin (1 + 2 * (2 : ℚ) ^ (-23 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f800001) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rn goes to the nearer neighbour
example : (Layout.binary 8 23 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-25 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-23 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rz on a positive number
example : (Layout.binary 8 23 true .ieee).round .rz .inf (1 + (2 : ℝ) ^ (-25 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rz on a negative number
example : (Layout.binary 8 23 true .ieee).round .rz .inf (-(1 + (2 : ℝ) ^ (-25 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rm on a positive number
example : (Layout.binary 8 23 true .ieee).round .rm .inf (1 + (2 : ℝ) ^ (-25 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rm) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rm on a negative number
example : (Layout.binary 8 23 true .ieee).round .rm .inf (-(1 + (2 : ℝ) ^ (-25 : ℤ))) false =
    some (.fin (-(1 + (2 : ℚ) ^ (-23 : ℤ)))) := by
  rw [Layout.round_between (m := .rm) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rp on a positive number
example : (Layout.binary 8 23 true .ieee).round .rp .inf (1 + (2 : ℝ) ^ (-25 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-23 : ℤ))) := by
  rw [Layout.round_between (m := .rp) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rp on a negative number
example : (Layout.binary 8 23 true .ieee).round .rp .inf (-(1 + (2 : ℝ) ^ (-25 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rp) (F := 0x3f800000) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: a subnormal value is exact
example : (Layout.binary 8 23 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-149 : ℤ)) false =
    some (.fin (3 * (2 : ℚ) ^ (-149 : ℤ))) := by
  rw [Layout.round_exact (m := .rn) (F := 3) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: half the smallest subnormal ties to the even zero
example : (Layout.binary 8 23 true .ieee).round .rn .inf ((2 : ℝ) ^ (-150 : ℤ)) false =
    some (.zero false) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: a negative number rounding to zero keeps its sign
example : (Layout.binary 8 23 true .ieee).round .rn .inf (-(2 : ℝ) ^ (-150 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: .rz of a tiny negative number is the negative zero
example : (Layout.binary 8 23 true .ieee).round .rz .inf (-(2 : ℝ) ^ (-151 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rz) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: a tie between subnormal codes 1 and 2 goes to 2
example : (Layout.binary 8 23 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-150 : ℤ)) false =
    some (.fin (2 * (2 : ℚ) ^ (-149 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 1) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: a value of the layout is exact
example : (Layout.binary 5 10 true .ieee).round .rn .inf (1) false =
    some (.fin 1) := by
  rw [Layout.round_exact (m := .rn) (F := 0x3c00) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: the midpoint above 1 goes to the even code 1
example : (Layout.binary 5 10 true .ieee).round .rn .inf (1 + (2 : ℝ) ^ (-11 : ℤ)) false =
    some (.fin 1) := by
  rw [Layout.round_between (m := .rn) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: the midpoint above the odd code goes up to the even code
example : (Layout.binary 5 10 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-11 : ℤ)) false =
    some (.fin (1 + 2 * (2 : ℚ) ^ (-10 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3c01) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rn goes to the nearer neighbour
example : (Layout.binary 5 10 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-12 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-10 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rz on a positive number
example : (Layout.binary 5 10 true .ieee).round .rz .inf (1 + (2 : ℝ) ^ (-12 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rz on a negative number
example : (Layout.binary 5 10 true .ieee).round .rz .inf (-(1 + (2 : ℝ) ^ (-12 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rm on a positive number
example : (Layout.binary 5 10 true .ieee).round .rm .inf (1 + (2 : ℝ) ^ (-12 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rm) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rm on a negative number
example : (Layout.binary 5 10 true .ieee).round .rm .inf (-(1 + (2 : ℝ) ^ (-12 : ℤ))) false =
    some (.fin (-(1 + (2 : ℚ) ^ (-10 : ℤ)))) := by
  rw [Layout.round_between (m := .rm) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rp on a positive number
example : (Layout.binary 5 10 true .ieee).round .rp .inf (1 + (2 : ℝ) ^ (-12 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-10 : ℤ))) := by
  rw [Layout.round_between (m := .rp) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rp on a negative number
example : (Layout.binary 5 10 true .ieee).round .rp .inf (-(1 + (2 : ℝ) ^ (-12 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rp) (F := 0x3c00) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: a subnormal value is exact
example : (Layout.binary 5 10 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-24 : ℤ)) false =
    some (.fin (3 * (2 : ℚ) ^ (-24 : ℤ))) := by
  rw [Layout.round_exact (m := .rn) (F := 3) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: half the smallest subnormal ties to the even zero
example : (Layout.binary 5 10 true .ieee).round .rn .inf ((2 : ℝ) ^ (-25 : ℤ)) false =
    some (.zero false) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: a negative number rounding to zero keeps its sign
example : (Layout.binary 5 10 true .ieee).round .rn .inf (-(2 : ℝ) ^ (-25 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: .rz of a tiny negative number is the negative zero
example : (Layout.binary 5 10 true .ieee).round .rz .inf (-(2 : ℝ) ^ (-26 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rz) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: a tie between subnormal codes 1 and 2 goes to 2
example : (Layout.binary 5 10 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-25 : ℤ)) false =
    some (.fin (2 * (2 : ℚ) ^ (-24 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 1) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: a value of the layout is exact
example : (Layout.binary 8 7 true .ieee).round .rn .inf (1) false =
    some (.fin 1) := by
  rw [Layout.round_exact (m := .rn) (F := 0x3f80) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: the midpoint above 1 goes to the even code 1
example : (Layout.binary 8 7 true .ieee).round .rn .inf (1 + (2 : ℝ) ^ (-8 : ℤ)) false =
    some (.fin 1) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: the midpoint above the odd code goes up to the even code
example : (Layout.binary 8 7 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-8 : ℤ)) false =
    some (.fin (1 + 2 * (2 : ℚ) ^ (-7 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f81) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rn goes to the nearer neighbour
example : (Layout.binary 8 7 true .ieee).round .rn .inf (1 + 3 * (2 : ℝ) ^ (-9 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-7 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rz on a positive number
example : (Layout.binary 8 7 true .ieee).round .rz .inf (1 + (2 : ℝ) ^ (-9 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rz on a negative number
example : (Layout.binary 8 7 true .ieee).round .rz .inf (-(1 + (2 : ℝ) ^ (-9 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rm on a positive number
example : (Layout.binary 8 7 true .ieee).round .rm .inf (1 + (2 : ℝ) ^ (-9 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rm) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rm on a negative number
example : (Layout.binary 8 7 true .ieee).round .rm .inf (-(1 + (2 : ℝ) ^ (-9 : ℤ))) false =
    some (.fin (-(1 + (2 : ℚ) ^ (-7 : ℤ)))) := by
  rw [Layout.round_between (m := .rm) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rp on a positive number
example : (Layout.binary 8 7 true .ieee).round .rp .inf (1 + (2 : ℝ) ^ (-9 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-7 : ℤ))) := by
  rw [Layout.round_between (m := .rp) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rp on a negative number
example : (Layout.binary 8 7 true .ieee).round .rp .inf (-(1 + (2 : ℝ) ^ (-9 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rp) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: a subnormal value is exact
example : (Layout.binary 8 7 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-133 : ℤ)) false =
    some (.fin (3 * (2 : ℚ) ^ (-133 : ℤ))) := by
  rw [Layout.round_exact (m := .rn) (F := 3) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: half the smallest subnormal ties to the even zero
example : (Layout.binary 8 7 true .ieee).round .rn .inf ((2 : ℝ) ^ (-134 : ℤ)) false =
    some (.zero false) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: a negative number rounding to zero keeps its sign
example : (Layout.binary 8 7 true .ieee).round .rn .inf (-(2 : ℝ) ^ (-134 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: .rz of a tiny negative number is the negative zero
example : (Layout.binary 8 7 true .ieee).round .rz .inf (-(2 : ℝ) ^ (-135 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rz) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: a tie between subnormal codes 1 and 2 goes to 2
example : (Layout.binary 8 7 true .ieee).round .rn .inf (3 * (2 : ℝ) ^ (-134 : ℤ)) false =
    some (.fin (2 * (2 : ℚ) ^ (-133 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 1) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: a value of the layout is exact
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (1) false =
    some (.fin 1) := by
  rw [Layout.round_exact (m := .rn) (F := 0x38) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: the midpoint above 1 goes to the even code 1
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (1 + (2 : ℝ) ^ (-4 : ℤ)) false =
    some (.fin 1) := by
  rw [Layout.round_between (m := .rn) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: the midpoint above the odd code goes up to the even code
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (1 + 3 * (2 : ℝ) ^ (-4 : ℤ)) false =
    some (.fin (1 + 2 * (2 : ℚ) ^ (-3 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x39) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rn goes to the nearer neighbour
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (1 + 3 * (2 : ℝ) ^ (-5 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-3 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rz on a positive number
example : (Layout.binary 4 3 true .e4m3).round .rz .satfinite (1 + (2 : ℝ) ^ (-5 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rz on a negative number
example : (Layout.binary 4 3 true .e4m3).round .rz .satfinite (-(1 + (2 : ℝ) ^ (-5 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rz) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rm on a positive number
example : (Layout.binary 4 3 true .e4m3).round .rm .satfinite (1 + (2 : ℝ) ^ (-5 : ℤ)) false =
    some (.fin (1)) := by
  rw [Layout.round_between (m := .rm) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rm on a negative number
example : (Layout.binary 4 3 true .e4m3).round .rm .satfinite (-(1 + (2 : ℝ) ^ (-5 : ℤ))) false =
    some (.fin (-(1 + (2 : ℚ) ^ (-3 : ℤ)))) := by
  rw [Layout.round_between (m := .rm) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rp on a positive number
example : (Layout.binary 4 3 true .e4m3).round .rp .satfinite (1 + (2 : ℝ) ^ (-5 : ℤ)) false =
    some (.fin (1 + (2 : ℚ) ^ (-3 : ℤ))) := by
  rw [Layout.round_between (m := .rp) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rp on a negative number
example : (Layout.binary 4 3 true .e4m3).round .rp .satfinite (-(1 + (2 : ℝ) ^ (-5 : ℤ))) false =
    some (.fin (-1)) := by
  rw [Layout.round_between (m := .rp) (F := 0x38) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: a subnormal value is exact
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (3 * (2 : ℝ) ^ (-9 : ℤ)) false =
    some (.fin (3 * (2 : ℚ) ^ (-9 : ℤ))) := by
  rw [Layout.round_exact (m := .rn) (F := 3) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: half the smallest subnormal ties to the even zero
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite ((2 : ℝ) ^ (-10 : ℤ)) false =
    some (.zero false) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: a negative number rounding to zero keeps its sign
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (-(2 : ℝ) ^ (-10 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rn) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: .rz of a tiny negative number is the negative zero
example : (Layout.binary 4 3 true .e4m3).round .rz .satfinite (-(2 : ℝ) ^ (-11 : ℤ)) false =
    some (.zero true) := by
  rw [Layout.round_between (m := .rz) (F := 0) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- e4m3: a tie between subnormal codes 1 and 2 goes to 2
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite (3 * (2 : ℝ) ^ (-10 : ℤ)) false =
    some (.fin (2 * (2 : ℚ) ^ (-9 : ℤ))) := by
  rw [Layout.round_between (m := .rn) (F := 1) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]
-- f32: the `.rn` overflow threshold MAX + ulp/2 gives the infinity
example : (Layout.binary 8 23 true .ieee).round .rn .inf
    ((2 - (2:ℝ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ) + (2:ℝ) ^ (103 : ℤ)) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: below the `.rn` threshold the result is MAX_NORM
example : (Layout.binary 8 23 true .ieee).round .rn .inf
    ((2 - (2:ℝ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ) + (2:ℝ) ^ (103 : ℤ) / 2) false =
    some (.fin ((2 - (2:ℚ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rn` overflow of a negative number gives the negative infinity
example : (Layout.binary 8 23 true .ieee).round .rn .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rz` never overflows
example : (Layout.binary 8 23 true .ieee).round .rz .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.fin ((2 - (2:ℚ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rz` never overflows, negative side
example : (Layout.binary 8 23 true .ieee).round .rz .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.fin (-((2 - (2:ℚ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ)))) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rm` on a positive number gives MAX_NORM
example : (Layout.binary 8 23 true .ieee).round .rm .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.fin ((2 - (2:ℚ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rm` on a negative number gives the negative infinity
example : (Layout.binary 8 23 true .ieee).round .rm .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rp` on a positive number gives the infinity
example : (Layout.binary 8 23 true .ieee).round .rp .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f32: `.rp` on a negative number gives -MAX_NORM
example : (Layout.binary 8 23 true .ieee).round .rp .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.fin (-((2 - (2:ℚ) ^ (-23 : ℤ)) * 2 ^ (127 : ℤ)))) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: the `.rn` overflow threshold MAX + ulp/2 gives the infinity
example : (Layout.binary 5 10 true .ieee).round .rn .inf (65504 + 16) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: below the `.rn` threshold the result is MAX_NORM
example : (Layout.binary 5 10 true .ieee).round .rn .inf (65504 + 16 / 2) false =
    some (.fin (65504)) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rn` overflow of a negative number gives the negative infinity
example : (Layout.binary 5 10 true .ieee).round .rn .inf (-(2:ℝ) ^ (17 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rz` never overflows
example : (Layout.binary 5 10 true .ieee).round .rz .inf ((2:ℝ) ^ (17 : ℤ)) false =
    some (.fin (65504)) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rz` never overflows, negative side
example : (Layout.binary 5 10 true .ieee).round .rz .inf (-(2:ℝ) ^ (17 : ℤ)) false =
    some (.fin (-(65504))) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rm` on a positive number gives MAX_NORM
example : (Layout.binary 5 10 true .ieee).round .rm .inf ((2:ℝ) ^ (17 : ℤ)) false =
    some (.fin (65504)) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rm` on a negative number gives the negative infinity
example : (Layout.binary 5 10 true .ieee).round .rm .inf (-(2:ℝ) ^ (17 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rp` on a positive number gives the infinity
example : (Layout.binary 5 10 true .ieee).round .rp .inf ((2:ℝ) ^ (17 : ℤ)) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- f16: `.rp` on a negative number gives -MAX_NORM
example : (Layout.binary 5 10 true .ieee).round .rp .inf (-(2:ℝ) ^ (17 : ℤ)) false =
    some (.fin (-(65504))) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: the `.rn` overflow threshold MAX + ulp/2 gives the infinity
example : (Layout.binary 8 7 true .ieee).round .rn .inf
    ((2 - (2:ℝ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ) + (2:ℝ) ^ (119 : ℤ)) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: below the `.rn` threshold the result is MAX_NORM
example : (Layout.binary 8 7 true .ieee).round .rn .inf
    ((2 - (2:ℝ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ) + (2:ℝ) ^ (119 : ℤ) / 2) false =
    some (.fin ((2 - (2:ℚ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rn` overflow of a negative number gives the negative infinity
example : (Layout.binary 8 7 true .ieee).round .rn .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rz` never overflows
example : (Layout.binary 8 7 true .ieee).round .rz .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.fin ((2 - (2:ℚ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rz` never overflows, negative side
example : (Layout.binary 8 7 true .ieee).round .rz .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.fin (-((2 - (2:ℚ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ)))) := by
  rw [Layout.round_inf_ieee (m := .rz) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rm` on a positive number gives MAX_NORM
example : (Layout.binary 8 7 true .ieee).round .rm .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.fin ((2 - (2:ℚ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ))) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rm` on a negative number gives the negative infinity
example : (Layout.binary 8 7 true .ieee).round .rm .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.inf true) := by
  rw [Layout.round_inf_ieee (m := .rm) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rp` on a positive number gives the infinity
example : (Layout.binary 8 7 true .ieee).round .rp .inf ((2:ℝ) ^ (129 : ℤ)) false =
    some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- bf16: `.rp` on a negative number gives -MAX_NORM
example : (Layout.binary 8 7 true .ieee).round .rp .inf (-(2:ℝ) ^ (129 : ℤ)) false =
    some (.fin (-((2 - (2:ℚ) ^ (-7 : ℤ)) * 2 ^ (127 : ℤ)))) := by
  rw [Layout.round_inf_ieee (m := .rp) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

-- An exact zero keeps the sign the caller supplies.
example : (Layout.binary 8 23 true .ieee).round .rn .inf 0 true = some (.zero true) :=
  Layout.round_zero (by trivial)

-- e4m3: `.satfinite` gives the sign-preserved MAX_NORM 448, decided on the input magnitude.
example : (Layout.binary 4 3 true .e4m3).round .rn .satfinite 460 false = some (.fin 448) := by
  rw [Layout.round_satfinite (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias]

example : (Layout.binary 4 3 true .e4m3).round .rp .satfinite (-1000) false =
    some (.fin (-448)) := by
  rw [Layout.round_satfinite (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias]

-- e4m3 has no infinity: with `Overflow.inf` an overflowing number has no result.
example : (Layout.binary 4 3 true .e4m3).round .rz .inf 1000 false = none :=
  Layout.round_inf_none (by decide)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])

-- An unsigned layout has no result for a negative number in range or for zero.
example : (Layout.binary 5 3 false .allOnesNaN).round .rn .satfinite (-1) false = none :=
  Layout.round_unsigned_below (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])

example : (Layout.binary 8 0 false .ue8m0).round .rz .satfinite 0 false = none :=
  Layout.round_unsigned_below (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])

-- ue8m0 with `.satfinite`: a magnitude above 2^127 of either sign gives the positive MAX_NORM.
example : (Layout.binary 8 0 false .ue8m0).round .rz .satfinite (-3.0e38) false =
    some (.fin ((2 : ℚ) ^ (127 : ℤ))) := by
  rw [Layout.round_satfinite (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias]

/-! `.s2f6`, the fixed-point layout `.fixed 8 6` -/

private abbrev s2f6 : Layout := .fixed 8 6

example : s2f6.round .rn .satfinite (-0.5) false = some (.fin (-1 / 2)) := by
  rw [Layout.round_fixed_exact (k := 32) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [Layout.fixedVal]

example : s2f6.round .rn .satfinite 0.5 false = some (.fin (1 / 2)) := by
  rw [Layout.round_fixed_exact (k := 32) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [Layout.fixedVal]

-- The patterns of `-0.5` and `+0.5` are `0xe0` and `0x20`.
example : s2f6.encode (.fin (-1 / 2)) = some 0xe0 :=
  Layout.encode_decode (by decide) (by norm_num [Layout.decode, Layout.width])

example : s2f6.encode (.fin (1 / 2)) = some 0x20 :=
  Layout.encode_decode (by decide) (by norm_num [Layout.decode, Layout.width])

-- Above `1.984375` `.satfinite` gives `127 * 2^-6`, the pattern `0x7f`.
example : s2f6.round .rn .satfinite 3 false = some (.fin (127 / 64)) := by
  rw [Layout.round_fixed_over (by simp) (by norm_num [Layout.maxNorm_fixed])]
  norm_num [Layout.maxNorm_fixed]

example : s2f6.encode (.fin (127 / 64)) = some 0x7f :=
  Layout.encode_decode (by decide) (by norm_num [Layout.decode, Layout.width])

-- Below `-1.984375` there is no result, including `-2.0` itself and `-1.99`.
example : s2f6.round .rn .satfinite (-2) false = none :=
  Layout.round_fixed_under (by norm_num [Layout.maxNorm_fixed])

example : s2f6.round .rz .satfinite (-1.99) false = none :=
  Layout.round_fixed_under (by norm_num [Layout.maxNorm_fixed])

-- `-1.984375` is a value: `-127 * 2^-6`, the pattern `0x81`.
example : s2f6.round .rn .satfinite (-1.984375) false = some (.fin (-127 / 64)) := by
  rw [Layout.round_fixed_exact (k := 127) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [Layout.fixedVal]

example : s2f6.encode (.fin (-127 / 64)) = some 0x81 :=
  Layout.encode_decode (by decide) (by norm_num [Layout.decode, Layout.width])

-- Ties go to the even integer; a negative number rounding to zero gives the one zero `+0`.
example : s2f6.round .rn .satfinite (3 / 128) false = some (.fin (2 / 64)) := by
  rw [Layout.round_fixed_between (k := 1) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [RoundMode.away, Layout.fixedVal]

example : s2f6.round .rn .satfinite (-1 / 128) false = some (.zero false) := by
  rw [Layout.round_fixed_between (k := 0) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [RoundMode.away, Layout.fixedVal]

example : s2f6.round .rm .satfinite (-1 / 100) false = some (.fin (-1 / 64)) := by
  rw [Layout.round_fixed_between (k := 0) (by simp) (by norm_num) (by norm_num)
    (by norm_num [Layout.maxNorm_fixed])]
  norm_num [RoundMode.away, Layout.fixedVal]

-- `.rs` has no result on the fixed-point layout.
example : s2f6.round (.rs 13 0) .satfinite 0.5 false = none := Layout.round_fixed_rs ..

/-! `.rs` to `.f16`: `1 + 2^-11` has `D = 2^12` discarded units of `2^-13` ulps. -/

private theorem rs_applies (r : Nat) (hr : r < 2 ^ 13) :
    (RoundMode.rs 13 r).applies (.binary 5 10 true .ieee) (1 + 2 ^ (-11 : ℤ)) := by
  refine ⟨hr, ⟨0x3F801000, 1 + 2 ^ (-11 : ℤ), ?_, by push_cast; ring⟩, Or.inr ?_⟩
  · norm_num [FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.expBits,
      FloatFmt.bias, FloatFmt.layout]
  · norm_num [Layout.minNormal, Layout.bias]

example : (Layout.binary 5 10 true .ieee).round (.rs 13 0) .inf (1 + 2 ^ (-11 : ℤ)) false =
    some (.fin 1) := by
  rw [Layout.round_between (F := 0x3C00) (rs_applies 0 (by norm_num)) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  rw [RoundMode.away_rs (D := 4096) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]

example : (Layout.binary 5 10 true .ieee).round (.rs 13 0x1FFF) .inf (1 + 2 ^ (-11 : ℤ)) false =
    some (.fin (1 + 2 ^ (-10 : ℤ))) := by
  rw [Layout.round_between (F := 0x3C00) (rs_applies 0x1FFF (by norm_num)) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  rw [RoundMode.away_rs (D := 4096) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]

-- `.rs` has no result for random bits of more than `k` bits.
example : (Layout.binary 5 10 true .ieee).round (.rs 13 0x2000) .inf 1 false = none := by
  simp [Layout.round, RoundMode.applies]

/-! `Layout.decode` on sample patterns of every layout. -/

example : FloatFmt.f32.layout.decode 0x7FC00000 = some (.nan (some 0x7FC00000)) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width]
example : FloatFmt.f32.layout.decode 0xFF800000 = some (.inf true) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width]
example : FloatFmt.f16.layout.decode 0x7C00 = some (.inf false) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width]
example : FloatFmt.f64.layout.decode 0x8000000000000000 = some (.zero true) :=
  FloatFmt.decode_signPattern .f64
example : FloatFmt.bf16.layout.decode 0 = some (.zero false) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width, Layout.fieldVal]
example : FloatFmt.e5m2.layout.decode (FloatFmt.e5m2.layout.infPattern true) = some (.inf true) :=
  FloatFmt.decode_infPattern .e5m2 (by decide) true
example : FloatFmt.e4m3.layout.decode 0x7f = some (.nan (some 0x7f)) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width]
example : FloatFmt.e4m3.layout.decode 0x7e = some (.fin 448) := by
  norm_num [Layout.decode, FloatFmt.layout, Layout.width, Layout.fieldVal, Layout.magnitude,
    Layout.bias]
example : (Layout.binary 8 0 false .ue8m0).decode 0 = none := by
  norm_num [Layout.decode, Layout.width]
example : (Layout.binary 8 0 false .ue8m0).decode 0xff = some (.nan (some 0xff)) := by
  norm_num [Layout.decode, Layout.width]
example : (Layout.binary 8 0 false .ue8m0).decode 0xfe = some (.fin (2 ^ (127 : ℤ))) := by
  norm_num [Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias]
example : (Layout.binary 5 3 false .allOnesNaN).decode 0xff = some (.nan (some 0xff)) := by
  norm_num [Layout.decode, Layout.width]
example : (Layout.binary 2 1 true .none).decode 0xf = some (.fin (-6)) := by
  norm_num [Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias]
example : s2f6.decode 0x80 = some (.fin (-2)) := by
  norm_num [Layout.decode, Layout.width]

-- `Layout.encode` inverts `Layout.decode` on small layouts.
example : (Layout.binary 2 1 true .none).encode (.fin (-6)) = some 0xf :=
  Layout.encode_decode (by decide)
    (by norm_num [Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias])
example : (Layout.binary 2 1 true .none).encode (.zero true) = some 0x8 :=
  Layout.encode_decode (by decide) (by norm_num [Layout.decode, Layout.width, Layout.fieldVal])

/-! The bits of a payload: `FloatFmt.encode` is the rounding, and `FloatFmt.encode_eq` states the
earlier formula. -/

example (fmt : FloatFmt) (x : ℝ) := FloatFmt.encode_eq fmt x

-- `1 + 2^-11` in `.f16` ties to the even code `0x3C00`.
example : FloatFmt.f16.encode (1 + 2 ^ (-11 : ℤ)) = 0x3C00 := by
  have h : FloatFmt.f16.layout.round .rn FloatFmt.f16.overflow (1 + 2 ^ (-11 : ℤ)) false =
      some (Layout.fieldVal FloatFmt.f16.expBits FloatFmt.f16.mantBits 0x3C00 false) := by
    show (Layout.binary 5 10 true .ieee).round .rn .inf _ false = _
    rw [Layout.round_between (m := .rn) (F := 0x3C00) (by trivial) (by decide)
      (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
      (by simp)]
    norm_num [RoundMode.away, Layout.magnitude, Layout.bias, FloatFmt.expBits,
      FloatFmt.mantBits, FloatFmt.layout]
  unfold FloatFmt.encode
  rw [h, Option.bind_some, FloatFmt.encode_fieldVal .f16 false (by decide)]
  rfl

-- A representable number's bits decode to the number.
example : FloatFmt.f32.layout.decode (FloatFmt.f32.encode (f32Value 0x3F800000).get!) =
    some (FVal.ofRat (f32Value 0x3F800000).get!) := by
  have h : f32Value 0x3F800000 = some 1 := by
    norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
      FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout]
  rw [h]
  exact FloatFmt.decode_encode_of_decode .f32 h

-- `.ftz`: a subnormal number flushes to the zero of its sign; a normal number is kept.
example : FloatFmt.f32.layout.flush (.fin (-(2 : ℚ) ^ (-140 : ℤ))) = .zero true := by
  norm_num [Layout.flush, Layout.subnormal, FloatFmt.layout, Layout.minNormal, Layout.bias]
example : FloatFmt.f32.layout.flush (.fin 1) = .fin 1 := by
  norm_num [Layout.flush, Layout.subnormal, FloatFmt.layout, Layout.minNormal, Layout.bias]

example : s2f6.maxNorm = 127 * 2 ^ (-6 : ℤ) := by norm_num [Layout.maxNorm_fixed]

end
end PTX.Tests.FloatRound
