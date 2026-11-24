-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # One site of the softmax warps' scan loop

Lane 31's total and the group's decision of the `loop2` scan (`.total .loop2`),
checked on its own so that the sites of the family build in parallel. The family theorem
is `stepAt_scan_loop2`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_loop2_total (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = []) (hs : d.site = .total .loop2) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
