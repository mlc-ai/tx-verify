-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScoreLib
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # One score load site of the softmax warps

The score load 0 of the bias round (`bias`), its own file so that the round's
loads check in parallel; the family theorem is `stepAt_sld`.
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_sld_bias_0 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = []) (hs : d.site = .sld .bias 0) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.sld _ _ => (by soft_sld)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
