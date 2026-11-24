-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedRoundContinuation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric

noncomputable section

/-- Values and register facts at the affine shift after an actual maximum and
correction publication. The state and suffix are shared by its consumers. -/
structure AffineRound (p : Params) (l : Launch) (X : Execution) (r : Repeated) (warp : Fin 8)
    (g j b h row blocks visit : Nat) (old : Option ℝ) (oldSum : ℝ) (chosen : Option ℝ)
    (phase : Nat) (entry : TState) (safe : Nat → Bool) where
  state : TState
  mixed : Bool
  words : Nat → Value
  scores : FmaItem → Option ℝ × Option ℝ
  atShift : At state r.affineStart []
  reads : ∀ i ∈ shiftItems r.shiftRound, ∀ n ∈ i.reads, state.regs n = some (words n)
  source : ∀ i ∈ shiftItems r.shiftRound, i.packOk words = true ∧
    splitValue 64 (i.src words) = (scoreValue (scores i).1, scoreValue (scores i).2)
  logits : ∀ i ∈ shiftItems r.shiftRound,
    (scores i).1 = maskedLogit p b h row (visitKey blocks visit (i.x-r.rawBase)) ∧
    (scores i).2 = maskedLogit p b h row (visitKey blocks visit (i.y-r.rawBase))
  scale : readERealPair l g state (.reg (shiftLayout r.shiftRound).scaleReg) =
    some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal)))
  offset : let reference := chosen.map (abiFloat p.scaleLog2Bits * ·)
    readERealPair l g state (.reg (shiftLayout r.shiftRound).addReg) =
      some (.ok (((-reference.getD 0 : ℝ) : EReal),((-reference.getD 0 : ℝ) : EReal)))
  frame : ∀ n ∈ r.numericFrame, state.regs n = some (words n)
  stage : r = .biased → words 637 = .pred ((stageOf warp).val = 1)
  mode : r = .biased → state.regs 634 = some (.pred mixed)
  warpWord : words 1062 = b32 warp.val
  base : words 2535 = b32 l.sharedBase
  addresses : r = .unbiased → ∀ q, words (probabilityReg .unbiased q) =
    b32 (probabilityAddress l g (stageOf warp) q)
  signal : r = .unbiased → words 5187 = b32 (l.sharedBase+8*(stageOf warp).val)
  oldMass : words 7257 = fl oldSum
  alpha : let scale := abiFloat p.scaleLog2Bits
    valFloat .f32 (words r.alphaReg) = .ok (maskedRescale (old.map (scale * ·))
      (chosen.map (scale * ·)))
  phaseWord : words 7258 = b32 phase
  maximum : state.regs 7256 = some (scoreValue chosen)
  keeps : ∀ n, safe n = true → state.regs n = entry.regs n
  suffix : Run kernel Assumptions.all l g state ((X.tr g).drop j) none

end
end PTX.Kernels.TmlFa4Fwd.Softmax
