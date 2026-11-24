-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Base
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The softmax warps' sub-steps that stay at their instruction

The elements of a bias load before the last (sub-steps 0 to 2), the implicit wait of a round's
first P store and a plain round's score load, all at sub-step 0. Its own file so that the three
families of `StepsMid.lean` check in parallel.

-/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_mid0 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : (∃ b c, d.site = .bld b c) ∨ d.site = .pst .first 0 ∨ d.site = .pst .bias 0 ∨
      ∃ c, d.site = .sld .plain c) :
    (codeD p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.pst _ _ => (by soft_tstw), .sld _ _ => (by soft_sldp)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
