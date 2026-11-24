-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.Exp2
public import Lemmas.Real.BlockSums
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace PTX.Numeric

open Finset

/-- Descending tiled traversal counts exactly the live prefix when the remaining slots
carry zero weight. -/
theorem sum_desc_masked {M : Type*} [AddCommMonoid M] (f : Nat → M)
    {tile blocks live : Nat} (h : live ≤ tile * blocks) :
    (∑ τ ∈ range blocks, ∑ j ∈ range tile,
      if tile * (blocks - 1 - τ) + j < live then f (tile * (blocks - 1 - τ) + j) else 0) =
      ∑ k ∈ range live, f k := by
  rw [sum_desc_blocks (fun k => if k < live then f k else 0) tile blocks]
  symm
  calc
    _ = ∑ k ∈ range live, if k < live then f k else 0 := by
      refine sum_congr rfl fun k hk => ?_
      rw [ite_eq_left (mem_range.mp hk)]
    _ = _ := by
      apply sum_subset (range_mono h)
      intro k _ hNot
      exact ite_eq_right (fun hlt => hNot (mem_range.mpr hlt))

/-- Online accumulation of weighted block sums, including masked slots with exactly zero
weight. Each intermediate result is relative to its current reference exponent. -/
theorem shifted_acc {n : Nat} {blockSum ref acc : Nat → ℝ}
    (h0 : acc 0 = (2 : ℝ) ^ (-ref 0) * blockSum 0)
    (hs : ∀ τ, τ + 1 < n → acc (τ + 1) = acc τ * (2 : ℝ) ^ (ref τ - ref (τ + 1)) +
      (2 : ℝ) ^ (-ref (τ + 1)) * blockSum (τ + 1)) :
    ∀ τ < n, acc τ = (2 : ℝ) ^ (-ref τ) * ∑ i ∈ range (τ + 1), blockSum i := by
  intro τ hτ
  induction τ with
  | zero => simpa using h0
  | succ τ ih =>
    have hFactor : (2 : ℝ) ^ (-ref τ) * (2 : ℝ) ^ (ref τ - ref (τ + 1)) =
        (2 : ℝ) ^ (-ref (τ + 1)) := by
      rw [← two_rpow_add]
      congr 1
      ring
    rw [hs τ hτ, ih (by omega)]
    calc
      _ = ((2 : ℝ) ^ (-ref τ) * (2 : ℝ) ^ (ref τ - ref (τ + 1))) *
          (∑ i ∈ range (τ + 1), blockSum i)
          + (2 : ℝ) ^ (-ref (τ + 1)) * blockSum (τ + 1) := by ring
      _ = _ := by rw [hFactor, sum_range_succ (n := τ + 1), mul_add]

/-- The row maximum cancels from LSE, before applying the ABI's natural-log multiplier. -/
theorem lse_cancel_reference (ref mass : ℝ) (h : 0 < mass) :
    ref + Real.logb 2 ((2 : ℝ) ^ (-ref) * mass) = Real.logb 2 mass := by
  rw [Real.logb_mul (two_rpow_ne_zero _) h.ne',
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
  ring

end PTX.Numeric
