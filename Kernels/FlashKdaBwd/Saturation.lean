-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Public
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # One-token gradient for the bounded-gate FLA call in checks/saturation.py -/
@[expose] public section
namespace FlashKda.Backward.Saturation
open Chunk Algorithm Sequence Finset
noncomputable section

def unitKey : Row 128 := fun i => if i = 0 then 1 else 0
def x (z : ℝ) : Tokens 128 :=
  activate (fun _ => unitKey) (fun _ => unitKey) (fun _ _ => 0) (fun _ => 2^30)
    (fun _ => z) (-1/2) 0 (fun _ => 0)
def firstOutput (z : ℝ) := output (x z) (fun _ => 0) 1 1 0

theorem ideal (z : ℝ) : firstOutput z = (2^30 / (1 + 1/1000000 : ℝ)) * sigmoid z := by
  rw [firstOutput, (forward (x z) _ 1 1).1 0 (by decide)]
  have hn : dot unitKey unitKey = 1 := by
    simp [dot, unitKey]
  have key (i : Fin 128) : Algorithm.normalize unitKey i =
      if i = 0 then 1 / Real.sqrt (1 + 1 / 1000000) else 0 := by
    simp only [Algorithm.normalize, hn, unitKey]
    split <;> simp
  simp [x, activate, tokenState, sequential, step, dot, key]
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (1 + 1 / 1000000 : ℝ))
  have hp : 0 < Real.sqrt (1 + 1 / 1000000 : ℝ) := by positivity
  field_simp
  nlinarith [congrArg (fun t : ℝ => t * sigmoid z) hs]

theorem derivative (z : ℝ) : HasDerivAt firstOutput
    ((2^30 / (1 + 1/1000000 : ℝ)) * sigmoidSlope z) z := by
  simp_rw [funext ideal]
  simpa only [mul_one] using! (sigmoid_deriv (hasDerivAt_id z)).const_mul
    (2^30 / (1 + 1/1000000 : ℝ))

/-- The real gradient exceeds two even though the public GPU backward returns zero. -/
theorem above_two : 2 < deriv firstOutput 20 := by
  rw [(derivative 20).deriv]
  have he : Real.exp 20 = (Real.exp 1)^20 := by
    simpa using Real.exp_nat_mul 1 20
  have lo : (480000000 : ℝ) < Real.exp 20 := by
    rw [he]
    exact lt_trans (by norm_num : (480000000 : ℝ) < 2.7182818283^20)
      (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by decide))
  have hi : Real.exp 20 < 490000000 := by
    rw [he]
    exact lt_trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide))
      (by norm_num : (2.7182818286 : ℝ)^20 < 490000000)
  unfold sigmoidSlope sigmoid
  rw [Real.exp_neg]
  have pos := Real.exp_pos 20
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hi.le) pos.le]

end
end FlashKda.Backward.Saturation
