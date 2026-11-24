-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # One half of the softmax warps' control sites

The biased rounds' polls (the score poll, the bias poll, the fence and the statistics
store) of `stepAt_bias_ctl`, its own file so that the control sites check in parallel.
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bias_ctl_poll (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .ws .bias
      ∨ d.site = .wb true
      ∨ d.site = .fence true
      ∨ d.site = .stat false) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
