-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.FiniteInputs
import Mathlib.Tactic

/-! Rounding the incoming FP32 state to bfloat16 can cancel a nonzero output even near one. -/
@[expose] public section
namespace FlashKda.Cancellation
open Chunk Sequence Algorithm Finset PTX
noncomputable section

def pair (a b : ℝ) : Row 128 := fun i =>
  (if i = 0 then a else 0) + (if i = 1 then b else 0)

theorem dot_pair (a b : ℝ) (y : Row 128) : dot (pair a b) y = a * y 0 + b * y 1 := by
  simp [dot, pair, add_mul, ite_mul, sum_add_distrib]

def inputs : Tokens 128 := activate (fun _ => pair 1 1) (fun _ _ => 0) (fun _ _ => 0)
  (fun _ => 0) (fun _ => 0) 0 0 (fun _ => 0)
def initial := pair (1+1/512) (-1)

theorem carries (t : ℕ) : tokenState inputs initial t = initial := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (tokenState inputs initial t) _ _ _ _ = _
    rw [ih]
    funext i
    simp [inputs, activate, step, Algorithm.normalize, logGate]

theorem real_output : output inputs initial 1 1 0 =
    1/512 / Real.sqrt (2+1/1000000) := by
  rw [(forward inputs initial 1 1).1 0 (by decide), carries]
  simp only [one_mul, initial, dot_pair, inputs, activate, Algorithm.normalize]
  norm_num [pair]
  ring

theorem relative_error_one : |0 - output inputs initial 1 1 0| / |output inputs initial 1 1 0| =
    1 := by
  rw [zero_sub, abs_neg, real_output, div_self]
  positivity

theorem rounds_away_increment : FloatFmt.bf16.layout.round .rn .inf ((1:ℝ)+1/512) false =
    some (.fin 1) := by
  change (Layout.binary 8 7 true .ieee).round .rn .inf _ false = _
  rw [Layout.round_between (m := .rn) (F := 0x3f80) (by trivial) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]

/-- Identical query coordinates cancel exactly with the bfloat16 state view at any common scale. -/
theorem quantized_read (q : Row 128) (h : q 0 = q 1) : dot (pair 1 (-1)) q = 0 := by
  rw [dot_pair, h]
  ring

end
end FlashKda.Cancellation
