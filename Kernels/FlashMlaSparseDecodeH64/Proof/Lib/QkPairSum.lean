-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QueryTile
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # The two lanes of a row pair cover the 512 features

The QK chain of the lane of row `r` of a 128-row tile sums the features
`feature k r t = 128 (k / 4) + 64 (r / 64) + 16 (k % 4) + t`, `k, t < 16`; the lane `r ^^^ 64`
(the same head, the other half of the contraction) sums the other 256 features. The two sums
are the sum over the 512 features (`pair_sum`). -/

/-! # The features of the two halves of a QK product

The contraction elements `(half, k, t)` (`half < 2` the 64-column half of the A row / B column,
`k < 16` the MMA, `t < 16` the element) are the 512 features exactly once:
`QueryTile.feature k (64 half) t = 128 (k / 4) + 64 half + 16 (k % 4) + t` (`sum_features`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile

open Finset

/-- **The two halves of a QK product cover the 512 features once.** -/
theorem sum_features (f : Nat → ℝ) :
    ∑ half ∈ range 2, ∑ k ∈ range 16, ∑ t ∈ range 16, f (feature k (64 * half) t) =
      ∑ i ∈ range 512, f i := by
  have h : ∑ x ∈ range 2 ×ˢ (range 16 ×ˢ range 16), f (feature x.2.1 (64 * x.1) x.2.2) =
      ∑ i ∈ range 512, f i := by
    refine Finset.sum_bij' (fun x _ => feature x.2.1 (64 * x.1) x.2.2)
      (fun i _ => (i / 64 % 2, (4 * (i / 128) + i % 64 / 16, i % 16))) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_product, mem_range] at hx ⊢
      simp only [feature]
      omega
    · intro i hi
      simp only [mem_product, mem_range] at hi ⊢
      omega
    · intro x hx
      obtain ⟨a, b, c⟩ := x
      simp only [mem_product, mem_range] at hx
      simp only [feature, Prod.mk.injEq]
      omega
    · intro i hi
      simp only [mem_range] at hi
      simp only [feature]
      omega
    · intro x hx
      rfl
  rw [← h, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_product]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile

open Finset

/-- **A row's half and its partner row's half** (`r < 128`). -/
theorem feature_half (r : Nat) (k t : Nat) :
    feature k r t = feature k (64 * (r / 64)) t := by
  simp only [feature]
  omega

/-- **The two lanes of a pair cover the features** (`r < 128`). -/
theorem pair_sum (f : Nat → ℝ) {r : Nat} (hr : r < 128) :
    ∑ k ∈ range 16, ∑ t ∈ range 16, f (feature k r t) +
      ∑ k ∈ range 16, ∑ t ∈ range 16, f (feature k (r ^^^ 64) t) = ∑ i ∈ range 512, f i := by
  have hx : (r ^^^ 64) / 64 = 1 - r / 64 := by
    have key : ∀ x < 128, (x ^^^ 64) / 64 = 1 - x / 64 := by decide
    exact key r hr
  have h2 : ∀ g : Nat → ℝ, ∑ h ∈ range 2, g h = g 0 + g 1 := fun g => by
    simp [Finset.sum_range_succ]
  rw [← sum_features f, h2]
  simp only [feature_half r, feature_half (r ^^^ 64), hx]
  have h : r / 64 = 0 ∨ r / 64 = 1 := by omega
  rcases h with h | h
  · rw [h]
  · rw [h, add_comm]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
