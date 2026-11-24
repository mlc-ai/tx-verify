-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Audit.OneTokenRound
import Mathlib.Tactic

/-! Sensitivity of the one-token witness to the hardware's permitted reciprocal square roots. -/
@[expose] public section
namespace FlashKda.OneToken
open PTX
noncomputable section

/-- Conservative relative error on ordinary positive inputs to the single-precision
approximate reciprocal square root. The NVIDIA PTX 9.2 limit is 2 to the power minus 22.9. -/
def admissibleRoot (x result : ℝ) := |result * Real.sqrt x - 1| ≤ 1/4194304

theorem root_interval {x a lo hi : ℝ} (hx : 0 < x) (hlo : 0 < lo) (hhi : 0 < hi)
    (result : admissibleRoot x a) (lower : lo^2*x < (1-1/4194304)^2)
    (upper : (1+1/4194304)^2 < hi^2*x) : lo < a ∧ a < hi := by
  obtain ⟨hm,hp⟩ := abs_le.mp result
  rw [← Real.sq_sqrt hx.le, ← mul_pow] at lower upper
  have h1 := (sq_lt_sq₀ (mul_pos hlo (Real.sqrt_pos.2 hx)).le (by norm_num)).mp lower
  have h2 := (sq_lt_sq₀ (by norm_num) (mul_pos hhi (Real.sqrt_pos.2 hx)).le).mp upper
  constructor
  · by_contra! contra
    linarith [mul_le_mul_of_nonneg_right contra (Real.sqrt_nonneg x)]
  · by_contra! contra
    linarith [mul_le_mul_of_nonneg_right contra (Real.sqrt_nonneg x)]

abbrev binary32 := Layout.binary 8 23 true .ieee
def epsilon32 : ℚ := 8796093/8796093022208

local macro "field_values" : tactic => `(tactic|
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, RoundMode.away, epsilon32])

theorem epsilon_value : binary32.decode 0x358637bd = some (.fin epsilon32) := by decide +kernel

theorem squared_norm_inputs :
    binary32.round .rn .inf ((3+1/1024 : ℝ)+epsilon32) false = some (.fin (3146753/1048576)) ∧
    binary32.round .rn .inf ((7/8+1/1024 : ℝ)+epsilon32) false =
      some (.fin (14696465/16777216)) := by
  constructor
  · rw [Layout.round_between (m := .rn) (F := 0x40401004) (by trivial) (by decide)
      (by field_values) (by field_values) (by simp)]
    field_values
  · rw [Layout.round_between (m := .rn) (F := 0x3f604010) (by trivial) (by decide)
      (by field_values) (by field_values) (by simp)]
    field_values

theorem query_scale {a : ℝ} (h : admissibleRoot (3146753/1048576) a) :
    5772/10000 < a ∧ a < 5774/10000 :=
  root_interval (by norm_num) (by norm_num) (by norm_num) h (by norm_num) (by norm_num)

theorem key_scale {a : ℝ} (h : admissibleRoot (14696465/16777216) a) :
    10684/10000 < a ∧ a < 10685/10000 :=
  root_interval (by norm_num) (by norm_num) (by norm_num) h (by norm_num) (by norm_num)

/-- Permit an absolute perturbation of 2 to the power minus 22 in each product before its
conversion to bfloat16. This includes the single-precision product errors at these magnitudes. -/
def conversionCell (center : ℝ) (encoded : ℚ) :=
  ∀ x : ℝ, |x-center| ≤ 1/4194304 → brainFloat.round .rn .inf x false = some (.fin encoded)

local macro "remove_abs" : tactic => `(tactic|
  first | rw [abs_of_pos (by linarith)] | rw [abs_of_neg (by linarith)])

local macro "round_cell" field:num : tactic => `(tactic| (
  rw [Layout.round_between (m := .rn) (F := $field) (by trivial) (by decide)
    (by remove_abs; norm_num [Layout.magnitude, Layout.bias]; linarith)
    (by remove_abs; norm_num [Layout.magnitude, Layout.bias]; linarith) (by simp)]
  remove_abs
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]
  split_ifs <;> norm_num [Layout.magnitude, Layout.bias] <;>
    (first | apply And.intro | skip) <;> linarith))

/-- Every pair of reciprocal square roots within the stated contract yields the recorded
normalized values, even allowing small independent errors in each pre-conversion product. -/
theorem normalized_values {q k : ℝ} (hq : admissibleRoot (3146753/1048576) q)
    (hk : admissibleRoot (14696465/16777216) k) :
    conversionCell q (37/64) ∧ conversionCell (-q) (-37/64) ∧
    conversionCell (-q/32) (-37/2048) ∧ conversionCell (k/4) (137/512) ∧
    conversionCell (k/2) (137/256) ∧ conversionCell (3*k/4) (205/256) ∧
    conversionCell (k/32) (137/4096) := by
  obtain ⟨ql, qu⟩ := query_scale hq
  obtain ⟨kl, ku⟩ := key_scale hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro x perturb
    obtain ⟨pl, pu⟩ := abs_le.mp perturb
  · round_cell 0x3f13
  · round_cell 0x3f13
  · round_cell 0x3c93
  · round_cell 0x3e88
  · round_cell 0x3f08
  · round_cell 0x3f4d
  · round_cell 0x3d08

end
end FlashKda.OneToken
