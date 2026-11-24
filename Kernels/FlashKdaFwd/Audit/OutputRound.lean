-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StateUpdate

/-! Normal single-precision values on opposite sides of a bfloat16 rounding boundary. -/
namespace FlashKda.Carry.Output
open PTX
noncomputable section

abbrev bf := Layout.binary 8 7 true .ieee
def initial : ℚ := 5657941/4194304
def delta : ℚ := -65/2^63
def halfway := initial * decay
def exactSum := halfway + delta
def lower : ℚ := 8486911/8388608
def upper : ℚ := 259/256

local macro "carry_values" : tactic => `(tactic|
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias, exactSum, halfway,
    initial, decay, delta, lower, upper])

local macro "round_between_fields" field:num : tactic => `(tactic| (
  rw [Layout.round_between (m := .rn) (F := $field) (by trivial) (by decide)
    (by carry_values) (by carry_values) (by simp)]
  carry_values))

theorem direct : singlePrecision.round .rn .inf (exactSum : ℝ) false = some (.fin lower) := by
  round_between_fields 0x3f817fff

theorem rounded_product : doublePrecision.round .rn .inf (halfway : ℝ) false =
    some (.fin halfway) := by
  rw [Layout.round_exact (m := .rn) (F := 0x3ff02ffff0000000) (by trivial) (by decide)
    (by decide) (by carry_values) (by simp)]
  carry_values

theorem rounded_sum : doublePrecision.round .rn .inf (exactSum : ℝ) false =
    some (.fin halfway) := by round_between_fields 0x3ff02fffefffffff

theorem narrowed : singlePrecision.round .rn .inf (halfway : ℝ) false =
    some (.fin upper) := by round_between_fields 0x3f817fff

theorem reference_state : referenceUpdate initial decay delta = some (.fin upper) := by
  unfold referenceUpdate
  change (do
    let .fin product ← doublePrecision.round .rn .inf (halfway : ℝ) false | none
    let .fin sum ← doublePrecision.round .rn .inf ((product+delta : ℚ) : ℝ) false | none
    singlePrecision.round .rn .inf (sum : ℝ) false) = _
  rw [rounded_product]
  change (do
    let .fin sum ← doublePrecision.round .rn .inf (exactSum : ℝ) false | none
    singlePrecision.round .rn .inf (sum : ℝ) false) = _
  rw [rounded_sum]
  exact narrowed

theorem round_exact_sum : FloatFmt.f32.layout.roundVal .rn true (.fin exactSum) =
    some (.fin lower) := by
  simp only [Layout.roundVal]
  unfold Layout.roundFtz
  rw [show FloatFmt.f32.layout = singlePrecision from rfl, direct]
  have magnitude : ¬ |(exactSum : ℝ)| < (singlePrecision.minNormal : ℚ) := by
    norm_num [Layout.minNormal, Layout.bias, exactSum, halfway, initial, decay, delta]
  simp [magnitude, show singlePrecision.flush (.fin lower) = .fin lower from by decide +kernel]

theorem production_state :
    update.lane [.fin initial, .fin decay, .fin delta] = some (.val (.fin lower)) := by
  apply evaluate (intermediate := .fin exactSum)
  · decide +kernel
  · decide +kernel
  · exact round_exact_sum

theorem next_tile_views :
    bf.round .rn .inf (lower : ℝ) false = some (.fin (129/128)) ∧
    bf.round .rn .inf (upper : ℝ) false = some (.fin (65/64)) := by
  constructor <;> round_between_fields 0x3f81

theorem bits :
    singlePrecision.decode 0x3facaaaa = some (.fin initial) ∧
    singlePrecision.decode 0xa3020000 = some (.fin delta) ∧
    singlePrecision.decode 0x3f817fff = some (.fin lower) ∧
    singlePrecision.decode 0x3f818000 = some (.fin upper) ∧
    bf.decode 0x3f81 = some (.fin (129/128)) ∧
    bf.decode 0x3f82 = some (.fin (65/64)) := by decide +kernel

end
end FlashKda.Carry.Output
