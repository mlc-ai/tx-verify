-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Lemmas.Flow.Step.SiteIte
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_start (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .setmax ∨ d.site = .bar1) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
