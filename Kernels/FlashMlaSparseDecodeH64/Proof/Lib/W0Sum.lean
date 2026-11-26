-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # The carried sum is the sum of the weights

The statistics a lane carries (`w0Carry`: the maximum `m` and the partial row sum `l`) keep the
invariant `l * 2 ^ m = Σ weights` of the columns the lane saw: a block rescales the old sum by
`2 ^ (m - m')` and adds its probabilities `2 ^ (sc s - m')`, whatever the new maximum `m'` is. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- The weight of a score: `2 ^ (sc s)`, zero for a dropped column. -/
def w0Wt (sc : ℝ) (s : EReal) : ℝ := if s = ⊥ then 0 else (2 : ℝ) ^ (sc * s.toReal)

/-- The weights of the 32 columns of a block. -/
def w0BlockWt (sc : ℝ) (seg : List Event) : ℝ :=
  ∑ i ∈ Finset.range 32, w0Wt sc (w0Score (w0Words seg) i)

/-- The weights of the columns of finished blocks. -/
def w0SumWt (sc : ℝ) (bs : List (List Event)) : ℝ := (bs.map (w0BlockWt sc)).sum

theorem w0Prob_mul (sc m : ℝ) (s : EReal) : w0Prob sc m s * (2 : ℝ) ^ m = w0Wt sc s := by
  unfold w0Prob w0Wt
  split_ifs
  · simp
  · rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring

theorem w0Next_wt (sc : ℝ) (ml : ℝ × ℝ) (w : W0Words) :
    (w0Next sc ml w).2 * (2 : ℝ) ^ (w0Next sc ml w).1 =
      ml.2 * (2 : ℝ) ^ ml.1 + ∑ i ∈ Finset.range 32, w0Wt sc (w0Score w i) := by
  unfold w0Next
  simp only
  rw [add_mul, mul_assoc, ← Real.rpow_add (by norm_num), Finset.sum_mul]
  have h : ml.1 - w0Max sc ml.1 w + w0Max sc ml.1 w = ml.1 := by ring
  rw [h]
  congr 1
  exact Finset.sum_congr rfl fun i _ => w0Prob_mul _ _ _

/-- **The carried-sum invariant**: `l * 2 ^ m` is the sum of the weights of the finished blocks. -/
theorem w0Carry_sum (sc : ℝ) (bs : List (List Event)) :
    (w0Carry sc bs).2 * (2 : ℝ) ^ (w0Carry sc bs).1 = w0SumWt sc bs := by
  induction bs using List.reverseRecOn with
  | nil => simp [w0Carry, w0SumWt]
  | append_singleton bs seg ih =>
    rw [w0Carry_snoc, w0Next_wt, ih]
    simp [w0SumWt, w0BlockWt]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
