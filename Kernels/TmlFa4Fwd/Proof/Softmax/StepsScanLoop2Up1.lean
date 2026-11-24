-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # One site of the softmax warps' scan loop

Prefix-sum step of the `loop2` scan (`.up .loop2 1`),
checked on its own so that the sites of the family build in parallel. The family theorem
is `stepAt_scan_loop2`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_scan_loop2_up1 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = []) (hs : d.site = .up .loop2 1) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
