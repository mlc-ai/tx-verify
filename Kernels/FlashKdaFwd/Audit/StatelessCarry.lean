-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StatelessDecode
import Kernels.FlashKdaFwd.Audit.OutputRound

namespace FlashKda.Stateless
open PTX Carry Carry.Output
noncomputable section

/-- The first state coordinate and per-tile decay at the second update in the reference trace. -/
def incoming : ℚ := 3/2
def multiplier : ℚ := 5657941/8388608

theorem operand_bits :
    singlePrecision.decode 0x3fc00000 = some (.fin incoming) ∧
    singlePrecision.decode 0x3f2caaaa = some (.fin multiplier) ∧
    singlePrecision.decode 0xa3020000 = some (.fin delta) := by decide +kernel

theorem machine_update :
    carryUpdate.lane [.fin incoming, .fin multiplier, .fin delta] = some (.val (.fin lower)) := by
  change Carry.update.lane _ = _
  apply Carry.evaluate (intermediate := .fin exactSum)
  · decide +kernel
  · decide +kernel
  · exact round_exact_sum

theorem reference_update : referenceUpdate incoming multiplier delta = some (.fin upper) := by
  rw [referenceUpdate, show incoming * multiplier = initial * decay by decide +kernel]
  exact reference_state

/-- At the recorded operands, the PTX site and reference give different next-tile views. -/
theorem second_tile :
    ∃ f : FloatInstr, carrySite = some ⟨none, .float f⟩ ∧
      f.lane [.fin incoming, .fin multiplier, .fin delta] = some (.val (.fin lower)) ∧
      referenceUpdate incoming multiplier delta = some (.fin upper) ∧
      bf.round .rn .inf (lower : ℝ) false = some (.fin (129/128)) ∧
      bf.round .rn .inf (upper : ℝ) false = some (.fin (65/64)) :=
  ⟨carryUpdate, decode_carry, machine_update, reference_update, next_tile_views⟩

end
end FlashKda.Stateless
