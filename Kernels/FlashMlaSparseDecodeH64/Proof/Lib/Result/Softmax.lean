-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.Exp2
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-! # Sparse online softmax in base 2

The kernel visits `n` blocks of `b` slots each; slot `(τ, j)` has an unnormalized weight
`w τ j = 2 ^ (scale · score)` for a valid slot and `0` for an invalid one, and value `v τ j`.
After block `τ` the accumulator holds `Σ w · v` and the row sum `Σ w` against a reference
exponent `c τ` (the thread's `mi`): the first block writes the terms against `c 0`, each later
block rescales by `2 ^ (c τ - c (τ + 1))` and adds its terms against `c (τ + 1)`.

Unlike `Lemmas/Real/Softmax.lean`, an invalid slot contributes zero rather than a score with
`-inf` weight, so the sums are over a weight function. The reference factors out, the ratio of
the final accumulator and row sum (plus the sink term) is the sparse softmax average, and the
final reference plus the log row sum is the natural log of `Σ w`.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX.Numeric

open Finset

/-- **Sparse max-agnostic accumulation.** -/
theorem sparse_acc {n b : ℕ} {w v : ℕ → ℕ → ℝ} {c S : ℕ → ℝ}
    (h0 : S 0 = ∑ j ∈ range b, w 0 j * 2 ^ (-c 0) * v 0 j)
    (hs : ∀ τ, τ + 1 < n → S (τ + 1) = S τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, w (τ + 1) j * 2 ^ (-c (τ + 1)) * v (τ + 1) j) :
    ∀ τ < n, S τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b,
      w τ' j * v τ' j := by
  intro τ hτ
  induction τ with
  | zero =>
    rw [h0, Finset.sum_range_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  | succ τ ih =>
    rw [hs τ hτ, ih (by omega)]
    have hsplit : (∑ τ' ∈ range (τ + 1 + 1), ∑ j ∈ range b, w τ' j * v τ' j) =
        (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j * v τ' j) +
          ∑ j ∈ range b, w (τ + 1) j * v (τ + 1) j := by
      rw [Finset.sum_range_succ]
    have hβ : (2 : ℝ) ^ (-c τ) * 2 ^ (c τ - c (τ + 1)) = 2 ^ (-c (τ + 1)) := by
      rw [← two_rpow_add]
      congr 1
      ring
    rw [hsplit, mul_add, mul_assoc,
      mul_comm (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j * v τ' j)
        (2 ^ (c τ - c (τ + 1))), ← mul_assoc, hβ]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The row sum of the sparse accumulator. -/
theorem sparse_sum {n b : ℕ} {w : ℕ → ℕ → ℝ} {c l : ℕ → ℝ}
    (h0 : l 0 = ∑ j ∈ range b, w 0 j * 2 ^ (-c 0))
    (hs : ∀ τ, τ + 1 < n → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, w (τ + 1) j * 2 ^ (-c (τ + 1))) :
    ∀ τ < n, l τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j := by
  intro τ hτ
  have h := sparse_acc (n := n) (v := fun _ _ => 1) (S := l) (by simpa using h0)
    (by simpa using hs) τ hτ
  simpa using h

/-- **The sparse ratio does not depend on the references.** -/
theorem sparse_ratio {n b : ℕ} {w v : ℕ → ℕ → ℝ} {c O l : ℕ → ℝ}
    (hO : ∀ τ < n, O τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b,
      w τ' j * v τ' j)
    (hl : ∀ τ < n, l τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j)
    {τ : ℕ} (hτ : τ < n) :
    O τ / l τ =
      (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j * v τ' j) /
        ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j := by
  rw [hO τ hτ, hl τ hτ, mul_div_mul_left _ _ (two_rpow_ne_zero (-c τ))]

/-- **The sparse final ratio with the sink term.** -/
theorem sparse_final_sink {_n b : ℕ} {w v : ℕ → ℕ → ℝ} {c O l : ℕ → ℝ} {sinkLog2 : ℝ}
    (hO : ∀ τ < _n, O τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b,
      w τ' j * v τ' j)
    (hl : ∀ τ < _n, l τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j)
    {τ : ℕ} (hτ : τ < _n) :
    O τ / (l τ + 2 ^ (sinkLog2 - c τ)) =
      (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j * v τ' j) /
        (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j + 2 ^ sinkLog2) := by
  rw [hO τ hτ, hl τ hτ, two_rpow_sub_eq_mul]
  have hden : 2 ^ (-c τ) * (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j) +
      2 ^ sinkLog2 * 2 ^ (-c τ) =
      2 ^ (-c τ) * (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j + 2 ^ sinkLog2) := by
    ring
  rw [hden, mul_div_mul_left _ _ (two_rpow_ne_zero (-c τ))]

/-- **The natural log of the sparse row sum** from the final reference and row sum. -/
theorem sparse_final_lse {b : ℕ} {w : ℕ → ℕ → ℝ} {c l : ℕ → ℝ} {τ : ℕ}
    (hl : l τ = 2 ^ (-c τ) * ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j)
    (hpos : 0 < ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j) :
    c τ * Real.log 2 + Real.log (l τ) =
      Real.log (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, w τ' j) := by
  rw [hl, Real.log_mul (two_rpow_ne_zero (-c τ)) hpos.ne', Real.log_rpow two_pos]
  ring

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
