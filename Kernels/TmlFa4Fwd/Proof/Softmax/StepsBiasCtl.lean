-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasCtlPoll
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' control sites of one round

The biased rounds' control sites before the P part (`stepAt_bias_ctl`, the polls in
`StepsBiasCtlPoll.lean`). The P part's control sites read the P part's data table, so they are
lifted from the control machine (`StepsBiasP.lean`).
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bias_ctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .ws .bias ∨ d.site = .wb true ∨ d.site = .fence true ∨ d.site = .stat false) :
    (codeD p L g).StepAt d :=
  stepAt_bias_ctl_poll hp _hg d hk ha hs

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
