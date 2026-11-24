-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Round
import Mathlib.Tactic

/-! The fused state update and the upstream binary64 implementation round to adjacent
binary32 results on finite, normal operands. -/
@[expose] public section
namespace FlashKda.Carry
open PTX
noncomputable section

abbrev singlePrecision := Layout.binary 8 23 true .ieee
abbrev doublePrecision := Layout.binary 11 52 true .ieee

def oldState : ℚ := 3/2 + 1/2^22
def decay : ℚ := 3/4
def correction : ℚ := -9/2^60
def midpoint := oldState * decay
def exactUpdate := midpoint + correction
def lowerNeighbor : ℚ := 9437185/8388608
def upperNeighbor : ℚ := 4718593/4194304

/-- The exact updated state lies just below the midpoint between adjacent FP32 values. -/
theorem interval :
    lowerNeighbor < exactUpdate ∧ exactUpdate < midpoint ∧
      midpoint = (lowerNeighbor + upperNeighbor)/2 := by decide +kernel

theorem single_round :
    singlePrecision.round .rn .inf (exactUpdate : ℝ) false = some (.fin lowerNeighbor) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f900001) (by trivial) (by decide)
    (by norm_num [exactUpdate, midpoint, oldState, decay, correction,
      Layout.magnitude, Layout.bias])
    (by norm_num [exactUpdate, midpoint, oldState, decay, correction,
      Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias, exactUpdate,
    midpoint, oldState, decay, correction, lowerNeighbor]

theorem double_product :
    doublePrecision.round .rn .inf (midpoint : ℝ) false = some (.fin midpoint) := by
  rw [Layout.round_exact (m := .rn) (F := 0x3ff2000030000000) (by trivial) (by decide)
    (by decide) (by norm_num [midpoint, oldState, decay, Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, midpoint, oldState, decay]

theorem double_sum :
    doublePrecision.round .rn .inf (exactUpdate : ℝ) false = some (.fin midpoint) := by
  rw [Layout.round_between (m := .rn) (F := 0x3ff200002fffffff) (by trivial) (by decide)
    (by norm_num [exactUpdate, midpoint, oldState, decay, correction,
      Layout.magnitude, Layout.bias])
    (by norm_num [exactUpdate, midpoint, oldState, decay, correction,
      Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias, exactUpdate,
    midpoint, oldState, decay, correction]

theorem narrowed_midpoint :
    singlePrecision.round .rn .inf (midpoint : ℝ) false = some (.fin upperNeighbor) := by
  rw [Layout.round_between (m := .rn) (F := 0x3f900001) (by trivial) (by decide)
    (by norm_num [midpoint, oldState, decay, Layout.magnitude, Layout.bias])
    (by norm_num [midpoint, oldState, decay, Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias, midpoint,
    oldState, decay, upperNeighbor]

/-- The upstream helper computes a product and sum in binary64 and narrows to binary32. -/
def referenceUpdate (a b c : ℚ) : Option FVal := do
  let .fin product ← doublePrecision.round .rn .inf ((a*b : ℚ) : ℝ) false | none
  let .fin sum ← doublePrecision.round .rn .inf ((product+c : ℚ) : ℝ) false | none
  singlePrecision.round .rn .inf (sum : ℝ) false

theorem reference_rounds_up :
    referenceUpdate oldState decay correction = some (.fin upperNeighbor) := by
  unfold referenceUpdate
  change (do
    let .fin product ← doublePrecision.round .rn .inf (midpoint : ℝ) false | none
    let .fin sum ← doublePrecision.round .rn .inf ((product+correction : ℚ) : ℝ) false | none
    singlePrecision.round .rn .inf (sum : ℝ) false) = _
  rw [double_product]
  change (do
    let .fin sum ← doublePrecision.round .rn .inf (exactUpdate : ℝ) false | none
    singlePrecision.round .rn .inf (sum : ℝ) false) = _
  rw [double_sum]
  exact narrowed_midpoint

theorem adjacent_bits : singlePrecision.decode 0x3f900001 = some (.fin lowerNeighbor) ∧
    singlePrecision.decode 0x3f900002 = some (.fin upperNeighbor) ∧
    upperNeighbor - lowerNeighbor = 1/2^23 := by decide +kernel

/-- All three recorded operands and both neighboring results have ordinary, nonzero FP32 values. -/
theorem operand_bits :
    singlePrecision.decode 0x3fc00002 = some (.fin oldState) ∧
    singlePrecision.decode 0x3f400000 = some (.fin decay) ∧
    singlePrecision.decode 0xa3100000 = some (.fin correction) := by decide +kernel

/-- For the underflow example, half the smallest normal is exactly representable in binary32. -/
theorem half_smallest :
    singlePrecision.round .rn .inf ((1:ℝ)/2^127) false = some (.fin (1/2^127)) := by
  rw [Layout.round_exact (m := .rn) (F := 0x400000) (by trivial) (by decide) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]

end
end FlashKda.Carry
