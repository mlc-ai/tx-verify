-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRolePrefix
public import Kernels.TmlFa4Fwd.Proof.NonzeroRoleCounts
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRoleCounts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX Prologue

noncomputable section

/-- The combined budget of the softmax, correction, MMA and output lanes. -/
def computeBudget (p : Params) : Nat :=
  (Softmax.softmaxRoleBudget p + 70) +
    (Correction.correctionTileBudget + 128 * (p.batch + 1) + 715) +
    (256 * 2 ^ 32 + 128 * (p.batch + 1) + 1371) +
    (128 * (p.batch + 1) + 1006)

private theorem component_le_sum (a b c d : Nat) :
    a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧
      c ≤ a + b + c + d ∧ d ≤ a + b + c + d := by omega

/-- All warps below the two loader warps have a common trace budget. -/
theorem computeLaneTraceBound {p : Params} {l : Launch} {m : Mem0} {X : Execution} {g : Nat}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hg : g < l.threads) (hw : warpIndex l g < 14) :
    (X.tr g).countP Event.counts ≤ computeBudget p := by
  have hb := component_le_sum (Softmax.softmaxRoleBudget p + 70)
    (Correction.correctionTileBudget + 128 * (p.batch + 1) + 715)
    (256 * 2 ^ 32 + 128 * (p.batch + 1) + 1371) (128 * (p.batch + 1) + 1006)
  by_cases hS : warpIndex l g < 8
  · exact (softmaxLaneTraceBound hp hX hg hS).trans hb.1
  by_cases hC : warpIndex l g < 12
  · exact (Correction.correctionLaneTraceBound hp hX hg (by omega) hC).trans hb.2.1
  by_cases hM : warpIndex l g = 12
  · exact (mmaLaneTraceBound hp hX hg hM).trans hb.2.2.1
  exact (epilogueLaneTraceBound hp hX hg (by omega)).trans hb.2.2.2

end
end PTX.Kernels.TmlFa4Fwd
