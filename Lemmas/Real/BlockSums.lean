-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Finite sums over blocks, in descending block order

A proof tool for kernels that visit `n` blocks of `b` consecutive indices, last block first
(FlashAttention's KV loop): a sum over the visit order `t < n` of block `n - 1 - t` is the sum
over the blocks (`sum_range_desc`), a sum over `b · n` indices is the sum over the blocks of
the sums over their offsets (`sum_range_blocks`, and `sum_fin_blocks` over `Fin`), and the two
together (`sum_desc_blocks`). -/

namespace PTX.Numeric

open Finset

variable {M : Type*} [AddCommMonoid M]

/-- Visiting `n` items last first sums the same. -/
theorem sum_range_desc (f : ℕ → M) (n : ℕ) :
    ∑ t ∈ range n, f (n - 1 - t) = ∑ j ∈ range n, f j :=
  Finset.sum_range_reflect f n

/-- A sum over `b · n` indices is the sum over `n` blocks of `b` consecutive indices. -/
theorem sum_range_blocks (f : ℕ → M) (b n : ℕ) :
    ∑ k ∈ range (b * n), f k = ∑ blk ∈ range n, ∑ c ∈ range b, f (b * blk + c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- `sum_range_blocks` over `Fin` indices. -/
theorem sum_fin_blocks (f : ℕ → M) (b n : ℕ) :
    ∑ k : Fin (b * n), f k = ∑ blk : Fin n, ∑ c : Fin b, f (b * blk + c) := by
  rw [Fin.sum_univ_eq_sum_range f, sum_range_blocks,
    ← Fin.sum_univ_eq_sum_range (fun blk => ∑ c ∈ range b, f (b * blk + c))]
  refine Finset.sum_congr rfl fun blk _ => ?_
  exact (Fin.sum_univ_eq_sum_range (fun c => f (b * blk + c)) b).symm

/-- **Descending blocks**: visiting the `n` blocks of `b` indices last first sums over all
`b · n` indices. -/
theorem sum_desc_blocks (f : ℕ → M) (b n : ℕ) :
    ∑ t ∈ range n, ∑ c ∈ range b, f (b * (n - 1 - t) + c) = ∑ k ∈ range (b * n), f k := by
  rw [sum_range_blocks]
  exact sum_range_desc (fun blk => ∑ c ∈ range b, f (b * blk + c)) n

end PTX.Numeric
