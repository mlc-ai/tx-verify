-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal6
public import Kernels.InklingRelDecode.Proof.Lib.EvWord
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

@[expose] public section

/-! # The scale word of the launch is exactly `scale * log2 e` -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode

noncomputable section

/-- **The scale word is the float `scale * log2 e`.** -/
theorem scaleW_eq {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) :
    scaleW L = .float .f32 (Q.scale * log2eF32) := by
  have h := scaleVal_float (L := L) hp
  simp [scaleW, Lib.scaleWord, xFinal, XItem.upd, XItem.vals, Lib.scaleItem, fF, regsOf, mulL,
    fOpnd, lk, regOf, List.flatMap, mulE_fin h valFloat_log2e, okVal]

/-- **The scale word reads as `scale * log2 e`.** -/
theorem scaleW_ev {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) :
    Ev (scaleW L) ((Q.scale * log2eF32 : ℝ) : EReal) :=
  ⟨by rw [scaleW_eq hp, erealValue_coe], EReal.coe_ne_top _⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
