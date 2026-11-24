-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # One half of the softmax warps' control sites

The biased rounds' P stores, store waits, warp barrier, election and elected lane's
arrival of `stepAt_bias_ctl`, their own file.
-/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bias_ctl_store (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .pst .bias 2
      ∨ d.site = .pwst .bias 0
      ∨ d.site = .pst .bias 3
      ∨ d.site = .pwst .bias 1
      ∨ d.site = .pws .bias
      ∨ d.site = .pel .bias
      ∨ d.site = .parr2 .bias) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.pst _ _ => (by soft_tst)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
