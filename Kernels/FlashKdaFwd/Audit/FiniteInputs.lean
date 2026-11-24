-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Sequence
public import Core.Thread.Float
public import Core.Float.Round
import Mathlib.Tactic

/-! Real answers to the two finite-input hardware probes and the IEEE overflow in normalization. -/
@[expose] public section
namespace FlashKda.FiniteInputs
open PTX Chunk Algorithm Sequence Finset
noncomputable section

def zeroWith (parameter : ℝ) : Tokens 128 :=
  activate (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)
    (-5) parameter (fun _ => 0)

theorem zero_state_at (parameter : ℝ) (t : ℕ) :
    tokenState (zeroWith parameter) (fun _ => 0) t = fun _ => 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (tokenState (zeroWith parameter) _ t) _ _ _ _ = _
    rw [ih]
    funext i
    simp [zeroWith, activate, Algorithm.normalize, step, dot]

theorem zero_output_at (parameter : ℝ) (total t : ℕ) (scale : ℝ) (ht : t < total) :
    output (zeroWith parameter) (fun _ => 0) total scale t = 0 := by
  rw [(forward (zeroWith parameter) _ total scale).1 t ht, zero_state_at]
  simp [dot]

abbrev zeroCase := zeroWith 100

theorem zero_state (t : ℕ) : tokenState zeroCase (fun _ => 0) t = fun _ => 0 :=
  zero_state_at 100 t

theorem zero_output (t : ℕ) (ht : t < 16) : output zeroCase (fun _ => 0) 16 1 t = 0 :=
  zero_output_at 100 16 t 1 ht

def axis (v : ℝ) : Row 128 := fun i => if i = 0 then v else 0

def queryCase : Tokens 128 :=
  activate (fun _ => axis (2^64)) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => 0) (fun _ => 0) 0 0 (fun _ => 0)

theorem query_state (t : ℕ) : tokenState queryCase (axis 1) t = axis 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step (tokenState queryCase _ t) _ _ _ _ = _
    rw [ih]
    funext i
    simp [queryCase, activate, step, logGate, Algorithm.normalize]

theorem query_output (t : ℕ) (ht : t < 16) :
    (511:ℝ)/512 < output queryCase (axis 1) 16 1 t := by
  rw [(forward queryCase _ 16 1).1 t ht, query_state]
  simp [queryCase, activate, Algorithm.normalize, dot, axis, ite_mul]
  have hx : (0:ℝ) < Real.sqrt (2^64 * 2^64 + (1000000:ℝ)⁻¹) := by positivity
  rw [lt_div_iff₀ hx]
  have upper : Real.sqrt ((2:ℝ)^64 * 2^64 + (1000000:ℝ)⁻¹) ≤ 2^64+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  linarith

theorem query_at_most_one (t : ℕ) (ht : t < 16) :
    output queryCase (axis 1) 16 1 t ≤ 1 := by
  rw [(forward queryCase _ 16 1).1 t ht, query_state]
  simp [queryCase, activate, Algorithm.normalize, dot, axis, ite_mul]
  have pos : 0 < Real.sqrt ((2:ℝ)^64 * 2^64 + (1000000:ℝ)⁻¹) := by positivity
  apply (div_le_iff₀ pos).mpr
  rw [one_mul]
  apply Real.le_sqrt_of_sq_le
  norm_num

/-- Absolute error of the observed zero output at each live token in the first value channel. -/
theorem observed_zero_error (t : ℕ) (ht : t < 16) :
    (511:ℝ)/512 < |0 - output queryCase (axis 1) 16 1 t| := by
  have h := query_output t ht
  rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
  exact h

/-- The chosen query coordinate is exactly representable in the public BF16 input. -/
theorem finite_bf16 : FloatFmt.bf16.layout.decode 0x5f80 = some (.fin (2^64)) := by
  decide +kernel

/-- Its square overflows FP32 round-to-nearest, before the reciprocal square root. -/
theorem square_overflows : (Layout.binary 8 23 true .ieee).round .rn .inf
    ((2:ℝ)^64 * 2^64) false = some (.inf false) := by
  rw [Layout.round_inf_ieee (m := .rn) (by trivial)
    (by norm_num [Layout.maxNorm_binary, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias]

theorem inverse_norm_zero : ((rsqrtTable.lookup .posInf).map ARes.val) = some (FVal.zero false) :=
  rfl

end
end FlashKda.FiniteInputs
