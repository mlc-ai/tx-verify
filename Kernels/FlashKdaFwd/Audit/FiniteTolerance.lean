-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.FiniteInputs

/-! Absolute and relative error criteria require a numerical GPU result. On the
public all-zero input with log-gate parameter 100, both recorded output types contain NaN. -/
namespace FlashKda.FiniteInputs
open PTX Sequence
noncomputable section

def within (fmt : FloatFmt) (word : Nat) (expected absolute relative : ℝ) : Prop :=
  ∃ x : ℚ, (fmt.layout.decode word).bind FVal.num = some x ∧
    |(x:ℝ)-expected| ≤ absolute + relative*|expected|

theorem finite_parameter_words :
    FloatFmt.f32.layout.decode 0x42c80000 = some (.fin 100) ∧
    FloatFmt.f32.layout.decode 0xc0a00000 = some (.fin (-5)) ∧
    FloatFmt.f32.layout.decode 0x3f800000 = some (.fin 1) ∧
    FloatFmt.f32.layout.decode 0 = some (.zero false) ∧
    FloatFmt.bf16.layout.decode 0 = some (.zero false) := by decide +kernel

/-- For each output token and each state coordinate the exact values are zero.
No pair of real tolerances can make the two measured words close to these values. -/
theorem no_finite_tolerance (t : Fin 16) (i : Fin 128) (absolute relative : ℝ) :
    let o := output zeroCase (fun _ => 0) 16 1 t
    let state := tokenState zeroCase (fun _ => 0) 16 i
    o = 0 ∧ state = 0 ∧ ¬within .bf16 0x7fff o absolute relative ∧
      ¬within .f32 0x7fffffff state absolute relative := by
  have bo : (FloatFmt.bf16.layout.decode 0x7fff).bind FVal.num = none := by decide +kernel
  have bs : (FloatFmt.f32.layout.decode 0x7fffffff).bind FVal.num = none := by decide +kernel
  simp [within,bo,bs,zero_state,zero_output t t.isLt]

end
end FlashKda.FiniteInputs
