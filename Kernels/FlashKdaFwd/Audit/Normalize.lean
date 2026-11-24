-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Ptx
public import Kernels.FlashKdaFwd.Audit.FiniteInputs
public import Core.Source.Decode

/-! Floating-point results for two instructions taken from the fixed-length preparation entry. -/
@[expose] public section
namespace FlashKda.Normalize
open PTX

def square : FloatInstr :=
  { op := .fma, ty := ⟨.f32, 1⟩, rnd := some .rn, ftz := true
    dsts := [some 303], srcs := [.reg 271, .reg 271, .f32imm 0] }

def invRoot : FloatInstr :=
  { op := .rsqrt, ty := ⟨.f32, 1⟩, mode := .approx, ftz := true
    dsts := [some 336], srcs := [.reg 335] }

/-- Floating values before and after the fused square with zero accumulator. -/
theorem square_lane : square.lane [.fin (2^64), .fin (2^64), .zero false] =
    some (.val (.inf false)) := by
  have exactProduct : ((FVal.fin (2^64)).mul (.fin (2^64))).add .rn (.zero false) =
      .fin ((2:ℚ)^64 * 2^64) := by decide +kernel
  have rounded : FloatFmt.f32.layout.roundVal .rn true (.fin ((2:ℚ)^64 * 2^64)) =
      some (.inf false) := by
    unfold Layout.roundVal Layout.roundFtz
    push_cast
    rw [show FloatFmt.f32.layout = Layout.binary 8 23 true .ieee from rfl,
      FiniteInputs.square_overflows]
    simp [Layout.flush]
  change (FOut.val <$> square.arith _) = _
  have inputs : square.flushIn [.fin (2^64), .fin (2^64), .zero false] =
      [.fin (2^64), .fin (2^64), .zero false] := by decide +kernel
  simp [FloatInstr.arith, square, FloatRound.mode]
  unfold square at inputs
  rw [inputs]
  change FloatFmt.f32.layout.roundVal .rn true _ = _
  rw [exactProduct, rounded]

theorem inverse_lane : invRoot.lane [.inf false] = some (.val (.zero false)) := rfl

/-- On an ordinary positive normal input the current TxVerify table specifies no result. -/
theorem positive_one_unspecified : invRoot.lane [.fin 1] = none := by
  change (FOut.val <$> invRoot.approx [.fin 1]) = none
  have one : invRoot.flushIn [.fin 1] = [.fin 1] := by decide +kernel
  simp only [FloatInstr.approx, one]
  decide +kernel

end FlashKda.Normalize
