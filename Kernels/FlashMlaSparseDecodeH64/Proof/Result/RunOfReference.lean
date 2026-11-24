-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run

@[expose] public section

/-! # The closed-form row run for a given sequence of softmax references -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Finset

noncomputable section

private theorem scaled_sum_zero (c : Nat → ℝ) (f : Nat → Nat → ℝ) :
    (2 : ℝ) ^ (-c 0) * (∑ b ∈ range (0 + 1), ∑ j ∈ range topkBlock, f b j) =
      ∑ j ∈ range topkBlock, 2 ^ (-c 0) * f 0 j := by
  rw [show 0 + 1 = 1 by rfl, Finset.sum_range_one, Finset.mul_sum]

private theorem scaled_sum_step (c : Nat → ℝ) (f : Nat → Nat → ℝ) (b : Nat) :
    (2 : ℝ) ^ (-c (b + 1)) * (∑ a ∈ range (b + 1 + 1), ∑ j ∈ range topkBlock, f a j) =
      (2 : ℝ) ^ (-c b) * (∑ a ∈ range (b + 1), ∑ j ∈ range topkBlock, f a j) *
        2 ^ (c b - c (b + 1)) +
      ∑ j ∈ range topkBlock, 2 ^ (-c (b + 1)) * f (b + 1) j := by
  have hExp : -c b + (c b - c (b + 1)) = -c (b + 1) := by ring
  have hScale : (2 : ℝ) ^ (-c b) * 2 ^ (c b - c (b + 1)) = 2 ^ (-c (b + 1)) := by
    rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ)), hExp]
  rw [Finset.sum_range_succ, mul_add, Finset.mul_sum (s := range topkBlock)]
  congr 1
  rw [mul_right_comm, hScale]

/-- The reference scales the same prefix of weights and values in both row accumulators. -/
def Run.ofReference (P : Params) (e q h : Nat) (c : Nat → ℝ) : Run P e q h where
  c := c
  O b d := 2 ^ (-c b) *
    ∑ a ∈ range (b + 1), ∑ j ∈ range topkBlock, blockWeight P e q h a j * blockValue P e q a j d
  l b := 2 ^ (-c b) * ∑ a ∈ range (b + 1), ∑ j ∈ range topkBlock, blockWeight P e q h a j
  O_zero d := by
    rw [scaled_sum_zero c (fun a j => blockWeight P e q h a j * blockValue P e q a j d)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  O_step b _ d := by
    rw [scaled_sum_step c (fun a j => blockWeight P e q h a j * blockValue P e q a j d) b]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  l_zero := by
    rw [scaled_sum_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mul_comm _ _
  l_step b _ := by
    rw [scaled_sum_step]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mul_comm _ _

/-- The closed-form numerator recurrence holds at each successor index. -/
theorem Run.ofReference_O_succ (P : Params) (e q h : Nat) (c : Nat → ℝ) (b d : Nat) :
    (Run.ofReference P e q h c).O (b + 1) d =
      (Run.ofReference P e q h c).O b d * 2 ^ (c b - c (b + 1)) +
      ∑ j ∈ range topkBlock,
        blockWeight P e q h (b + 1) j * 2 ^ (-c (b + 1)) * blockValue P e q (b + 1) j d := by
  dsimp only [Run.ofReference]
  rw [scaled_sum_step c (fun a j => blockWeight P e q h a j * blockValue P e q a j d) b]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
