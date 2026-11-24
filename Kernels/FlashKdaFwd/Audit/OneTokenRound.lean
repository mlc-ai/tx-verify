-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.OneToken
public import Core.Float.Round
import Mathlib.Tactic

/-! Decode the bfloat16 values recorded from the device workspace and public output. -/
@[expose] public section
namespace FlashKda.OneToken
open PTX Chunk
noncomputable section

abbrev brainFloat := Layout.binary 8 7 true .ieee

theorem workspace_words :
    brainFloat.decode 0x3f14 = some (.fin (37/64)) ∧
    brainFloat.decode 0xbf14 = some (.fin (-37/64)) ∧
    brainFloat.decode 0xbc94 = some (.fin (-37/2048)) ∧
    brainFloat.decode 0x3e89 = some (.fin (137/512)) ∧
    brainFloat.decode 0x3f09 = some (.fin (137/256)) ∧
    brainFloat.decode 0x3f4d = some (.fin (205/256)) ∧
    brainFloat.decode 0x3d09 = some (.fin (137/4096)) ∧
    brainFloat.decode 0x3a0a = some (.fin (69/131072)) ∧
    brainFloat.decode 0x398a = some (.fin (69/262144)) ∧
    brainFloat.decode 0x3a00 = some (.fin (1/2048)) ∧
    brainFloat.decode 0x3a14 = some (.fin (37/65536)) := by decide +kernel

theorem workspace_dot :
    dot (four (37/64) (37/64) (-37/64) (-37/2048))
      (four (137/512) (137/256) (205/256) (137/4096)) = 4403/8388608 := by
  rw [dot_four]
  norm_num [four]

local macro "field_values" : tactic => `(tactic|
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, RoundMode.away])

theorem rounded_dot : brainFloat.round .rn .inf (4403/8388608 : ℝ) false =
    some (.fin (69/131072)) := by
  rw [Layout.round_between (m := .rn) (F := 0x3a09) (by trivial) (by decide)
    (by field_values) (by field_values) (by simp)]
  field_values

theorem rounded_output : brainFloat.round .rn .inf ((69/131072 : ℝ)/2) false =
    some (.fin (69/262144)) := by
  rw [Layout.round_exact (m := .rn) (F := 0x398a) (by trivial) (by decide)
    (by decide) (by field_values) (by simp)]
  field_values

theorem measured_sign_flip :
    answer (1/32) 1 < 0 ∧ 0 < (69/262144 : ℝ) :=
  ⟨negative (by norm_num) (by norm_num), by norm_num⟩

theorem no_relative_bound (constant : ℝ) :
    ¬ |37/65536 - answer 0 1| ≤ constant * |answer 0 1| := by
  rw [zero_exact]
  norm_num

/-- For the fourth component 1/64 the observed error exceeds seven times the true magnitude. -/
theorem sevenfold_error : 7 < |1/2048 - answer (1/64) 1| / |answer (1/64) 1| := by
  have hk : (9/10 : ℝ) < √(7/8+(1/64)^2+1/1000000) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hq : (17/10 : ℝ) < √(3+(1/64)^2+1/1000000) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hprod := mul_lt_mul_of_pos_right hk (by positivity :
    0 < Real.sqrt (3+(1/64 : ℝ)^2+1/1000000))
  have hprod' := mul_lt_mul_of_pos_left hq (by norm_num : (0:ℝ) < 9/10)
  have hden : 3 < 2 * Real.sqrt (7/8+(1/64 : ℝ)^2+1/1000000) *
      Real.sqrt (3+(1/64 : ℝ)^2+1/1000000) := by linarith
  have bound : -(1/12288 : ℝ) < answer (1/64) 1 := by
    rw [real_answer, lt_div_iff₀ (by linarith)]
    linarith
  have hx : answer (1/64) 1 < 0 := negative (by norm_num) (by norm_num)
  rw [abs_of_neg hx, abs_of_pos (by linarith), lt_div_iff₀ (by linarith)]
  linarith

end
end FlashKda.OneToken
