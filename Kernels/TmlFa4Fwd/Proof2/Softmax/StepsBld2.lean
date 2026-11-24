-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The softmax warps' sub-steps that stay at their instruction

The third element of a bias load (sub-step 2). Its own file so that the three families of
`StepsMid.lean` check in parallel.

-/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bld2 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 2) (ha : d.acc.length = 2) (hs : ∃ b c, d.site = .bld b c) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  match acc, ha with
  | [a, b], _ => soft_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
