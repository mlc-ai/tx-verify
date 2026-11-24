-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Spec
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # The kernel's arithmetic

The sums the code computes, in the order it computes them: the chain of fused multiply-adds of
a thread's sixteen inputs (`fmaSum`), and a running sum of received values (`bsum`), which is
what each round of a butterfly reduction leaves in a lane. A butterfly round adds to each lane
the value of the lane whose index differs in one bit (`bf`); the five rounds of a warp leave
every lane with the sum over the warp (`bfAll_eq`). -/

namespace PTX.Kernels.RmsNorm.Proof
open Finset

noncomputable section

/-- The chain `v (n-1)^2 + (... + (v 0^2 + z))` of fused multiply-adds. -/
def fmaSum (v : Nat → ℝ) : Nat → ℝ → ℝ
  | 0, z => z
  | n + 1, z => v n * v n + fmaSum v n z

/-- `q` after adding the first `k` received values `r 0, ..., r (k-1)`. -/
def bsum (q : ℝ) (r : Nat → ℝ) : Nat → ℝ
  | 0 => q
  | k + 1 => bsum q r k + r k

/-- One butterfly round: a lane's value plus the value of the lane `l xor d`. -/
def bf (d : Nat) (V : Nat → ℝ) (l : Nat) : ℝ := V l + V (l ^^^ d)

/-- The five rounds with offsets 16, 8, 4, 2, 1. -/
def bfAll (V : Nat → ℝ) : Nat → ℝ := bf 1 (bf 2 (bf 4 (bf 8 (bf 16 V))))

theorem fmaSum_eq (v : Nat → ℝ) (z : ℝ) : ∀ n, fmaSum v n z = z + ∑ m ∈ range n, v m ^ 2
  | 0 => by simp [fmaSum]
  | n + 1 => by rw [fmaSum, fmaSum_eq v z n, sum_range_succ]; ring

theorem bfAll_eq (V : Nat → ℝ) : bfAll V 0 = ∑ l ∈ range 32, V l := by
  simp only [bfAll, bf, sum_range_succ, sum_range_zero, Nat.reduceXor, zero_add]
  ring

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (f : Nat → M) (B : Nat) :
    ∀ A, ∑ a ∈ range A, ∑ b ∈ range B, f (B * a + b) = ∑ k ∈ range (A * B), f k
  | 0 => by simp
  | A + 1 => by
    rw [sum_range_succ, sum_range_mul f B A, Nat.succ_mul, sum_range_add, Nat.mul_comm A B]

end

end PTX.Kernels.RmsNorm.Proof
