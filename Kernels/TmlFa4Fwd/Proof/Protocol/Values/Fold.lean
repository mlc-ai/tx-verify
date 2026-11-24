-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-! # A row's running softmax

A row's tile-by-tile softmax: the probabilities of tile `u` are the weights `w u k` scaled by
`c u`, the row sum and the accumulator are rescaled by the factor `f u` before tile `u`, which is
`c u / c (u - 1)` unless every weight so far is zero (`Fold`). So the accumulator after tile `u` is
`c u` times the weighted sum of the values so far (`Fold.acc_eq`) and the last accumulator over the
row sum is the weighted mean (`Fold.mean`). The tiles visit the blocks from the last one
(`visit_sum`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values

noncomputable section

/-- **The running softmax of a row** of `n` tiles with weights `w`: the probabilities `P`, the
scales `c`, the rescaling factors `f` and the final row sum `rs`. -/
structure Fold (n : ℕ) (w P : ℕ → ℕ → ℝ) (c f : ℕ → ℝ) (rs : ℝ) : Prop where
  pos : ∀ u < n, 0 < c u
  prob : ∀ u < n, ∀ k < 128, P u k = c u * w u k
  factor : ∀ u, u + 1 < n → f (u + 1) = c (u + 1) / c u ∨ ∀ v ≤ u, ∀ k < 128, w v k = 0
  le : ∀ u < n, f u ≤ 1
  sum : rs = c (n - 1) * ∑ u ∈ Finset.range n, ∑ k ∈ Finset.range 128, w u k

/-- **The accumulator after tile `u`** of a chain that rescales by `f`. -/
theorem Fold.acc_eq {n : ℕ} {w P : ℕ → ℕ → ℝ} {c f : ℕ → ℝ} {rs : ℝ} (h : Fold n w P c f rs)
    {v : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (h0 : a 0 = ∑ k ∈ Finset.range 128, P 0 k * v 0 k)
    (hs : ∀ u, u + 1 < n → a (u + 1) = a u * f (u + 1) +
      ∑ k ∈ Finset.range 128, P (u + 1) k * v (u + 1) k) :
    ∀ u < n, a u = c u * ∑ t ∈ Finset.range (u + 1), ∑ k ∈ Finset.range 128, w t k * v t k := by
  have hterm : ∀ u < n, ∑ k ∈ Finset.range 128, P u k * v u k =
      c u * ∑ k ∈ Finset.range 128, w u k * v u k := by
    intro u hu
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h.prob u hu k (Finset.mem_range.mp hk)]
    ring
  intro u
  induction u with
  | zero =>
    intro hu
    rw [h0, hterm 0 hu, Finset.sum_range_one]
  | succ u ih =>
    intro hu
    rw [hs u hu, hterm (u + 1) hu, ih (by omega), Finset.sum_range_succ _ (u + 1), mul_add]
    congr 1
    rcases h.factor u hu with hf | hz
    · rw [hf]
      have := (h.pos u (by omega)).ne'
      field_simp
    · have : ∑ t ∈ Finset.range (u + 1), ∑ k ∈ Finset.range 128, w t k * v t k = 0 := by
        refine Finset.sum_eq_zero fun t ht => Finset.sum_eq_zero fun k hk => ?_
        rw [hz t (by have := Finset.mem_range.mp ht; omega) k (Finset.mem_range.mp hk), zero_mul]
      rw [this]
      ring

/-- **The last accumulator over the row sum is the weighted mean.** -/
theorem Fold.mean {n : ℕ} {w P : ℕ → ℕ → ℝ} {c f : ℕ → ℝ} {rs : ℝ} (h : Fold n w P c f rs)
    (hn : 0 < n) {x y : ℝ} (hx : x = c (n - 1) * y) :
    x * rs⁻¹ = y / ∑ u ∈ Finset.range n, ∑ k ∈ Finset.range 128, w u k := by
  have hc := (h.pos (n - 1) (by omega)).ne'
  rw [hx, h.sum, mul_inv, div_eq_mul_inv]
  field_simp

/-- **The blocks are visited from the last one.** -/
theorem visit_sum (n : ℕ) (g : ℕ → ℝ) :
    ∑ u ∈ Finset.range n, ∑ k ∈ Finset.range 128, g (128 * (n - 1 - u) + k) =
      ∑ j ∈ Finset.range (128 * n), g j := by
  rw [Finset.sum_range_reflect (fun u => ∑ k ∈ Finset.range 128, g (128 * u + k)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 128 * (n + 1) = 128 * n + 128 by ring,
      Finset.sum_range_add]

/-- A sum over the first keys of the visited blocks, the others' terms zero. -/
theorem visit_sum_lt {n m : ℕ} (hm : m ≤ 128 * n) (g : ℕ → ℝ) :
    ∑ u ∈ Finset.range n, ∑ k ∈ Finset.range 128,
        (if 128 * (n - 1 - u) + k < m then g (128 * (n - 1 - u) + k) else 0) =
      ∑ j ∈ Finset.range m, g j := by
  rw [visit_sum n (fun j => if j < m then g j else 0), ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The log of a scaled row sum. -/
theorem log_scaled {s m y : ℝ} (hy : 0 < y) :
    s * m + Real.logb 2 ((2 : ℝ) ^ (-(s * m)) * y) = Real.logb 2 y := by
  rw [Real.logb_mul (by positivity) hy.ne', Real.logb_rpow (by norm_num) (by norm_num)]
  ring

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
