-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.CarryDecode
import Kernels.FlashKdaFwd.Audit.CarryRound
import Core.Thread.Float

namespace FlashKda.Carry
open PTX
noncomputable section

/-- The decoded scalar operation with input flushing and rounding made explicit. -/
theorem evaluate {a b c intermediate result : FVal}
    (inputs : update.flushIn [a,b,c] = [a,b,c])
    (arithmetic : (a.mul b).add .rn c = intermediate)
    (rounded : FloatFmt.f32.layout.roundVal .rn true intermediate = some result) :
    update.lane [a,b,c] = some (.val result) := by
  change (FOut.val <$> update.arith _) = _
  simp [FloatInstr.arith, update, FloatRound.mode]
  unfold update at inputs
  rw [inputs]
  change FloatFmt.f32.layout.roundVal .rn true _ = _
  rw [arithmetic, rounded]

/-- Evaluate a production state update with normal inputs and a normal, nonzero result. -/
theorem rounds_down : update.lane [.fin oldState, .fin decay, .fin correction] =
    some (.val (.fin lowerNeighbor)) := by
  have inputs : update.flushIn [.fin oldState, .fin decay, .fin correction] =
      [.fin oldState, .fin decay, .fin correction] := by decide +kernel
  have arithmetic : ((FVal.fin oldState).mul (.fin decay)).add .rn (.fin correction) =
      .fin exactUpdate := by decide +kernel
  have rounded : FloatFmt.f32.layout.roundVal .rn true (.fin exactUpdate) =
      some (.fin lowerNeighbor) := by
    simp only [Layout.roundVal]
    unfold Layout.roundFtz
    rw [show FloatFmt.f32.layout = singlePrecision from rfl, single_round]
    have magnitude : ¬ |(exactUpdate : ℝ)| < (singlePrecision.minNormal : ℚ) := by
      norm_num [Layout.minNormal, Layout.bias, exactUpdate, midpoint, oldState, decay, correction]
    simp [magnitude, show singlePrecision.flush (.fin lowerNeighbor) = .fin lowerNeighbor
      from by decide +kernel]
  exact evaluate inputs arithmetic rounded

theorem flushes_half_minimum : update.lane [.fin (1/2^126), .fin (1/2), .zero false] =
    some (.val (.zero false)) := by
  have inputs : update.flushIn [.fin (1/2^126), .fin (1/2), .zero false] =
      [.fin (1/2^126), .fin (1/2), .zero false] := by decide +kernel
  have arithmetic : ((FVal.fin (1/2^126)).mul (.fin (1/2))).add .rn (.zero false) =
      .fin (1/2^127) := by decide +kernel
  have rounded : FloatFmt.f32.layout.roundVal .rn true (.fin (1/2^127)) =
      some (.zero false) := by
    simp only [Layout.roundVal]
    unfold Layout.roundFtz
    push_cast
    rw [show FloatFmt.f32.layout = singlePrecision from rfl, half_smallest]
    simp [-one_div, show singlePrecision.subnormal (1/2^127) = true from by decide +kernel,
      show singlePrecision.flush (.fin (1/2^127)) = .zero false from by decide +kernel]
  exact evaluate inputs arithmetic rounded

/-- At these ordinary FP32 operands the compiled update and the upstream helper differ. -/
theorem production_reference_difference : ∃ f : FloatInstr,
    site = some ⟨none, .float f⟩ ∧
    f.lane [.fin oldState, .fin decay, .fin correction] ≠
      (FOut.val <$> referenceUpdate oldState decay correction) := by
  refine ⟨update, decode_update, ?_⟩
  rw [rounds_down, reference_rounds_up]
  decide +kernel

end
end FlashKda.Carry
