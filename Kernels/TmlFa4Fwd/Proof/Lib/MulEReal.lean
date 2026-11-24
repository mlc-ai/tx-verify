-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal

@[expose] public section

/-! # An exact product with a finite left operand and `-∞`

A proof tool for promotion next to `Lemmas/Flow/Step/RuleStep.lean`'s `mulEReal_bot_pos` (which
has the infinity on the left): a positive real times `-∞` is `-∞` under the ideal rule. The
softmax warps' plain rounds multiply the exponent scale (left) by `-∞` (pc 6880) when the row
maximum before the round is `-∞`; with this fact in context the rule step evaluates. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof

/-- A positive real times `-∞` is `-∞`. -/
theorem mulEReal_coe_bot_pos {y : ℝ} (hy : 0 < y) :
    Assumption.mulEReal (y : EReal) ⊥ = some ⊥ := by
  simp [Assumption.mulEReal, hy.ne', EReal.coe_mul_bot_of_pos hy]

end PTX.Kernels.TmlFa4Fwd.Proof
