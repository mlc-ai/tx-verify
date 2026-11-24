-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsKeepB
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPw1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsKeepB2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrB
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsMaxB

@[expose] public section

/-! # The bias round's updated maximum -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32 addi xor32 scmpi)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (neg32)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem maxB_lt_top (p : Params) (v : V) : maxB p v < ⊤ := by
  unfold maxB
  split
  · exact EReal.coe_lt_top _
  · exact foldBE_lt_top p v

theorem maxB_word (p : Params) (v : V) :
    lookupD (valuesBiasM p v) 7256 = erealValue .f32 (maxB p v) := by
  change (bif v.mf then (if keepB p v = true then .float .f32 v.mr else .float .f32 (foldBR p v))
    else erealValue .f32 (foldBE p v)) = _
  unfold maxB
  cases hm : v.mf
  · simp only [Bool.cond_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.cond_true, Bool.true_and]
    split
    · rw [erealValue_coe]
    · rw [foldBE_real hm, erealValue_coe]

theorem mxVal_maxB (v : V) (x : ℝ) :
    mxVal (biasTailV v (finE (maxB p v)) (maxB p v).toReal x) =
      lookupD (valuesBiasM p v) 7256 := by
  rw [maxB_word]
  have htop := maxB_lt_top p v
  rcases eq_or_ne (maxB p v) ⊥ with h | h
  · rw [h, finE_bot, erealValue_bot]
    rfl
  · have e := EReal.coe_toReal htop.ne h
    conv => rhs; rw [← e]
    rw [erealValue_coe]
    unfold biasTailV
    have hf : finE (maxB p v) = true := by simp [finE, h]
    simp only [mxVal, hf]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
