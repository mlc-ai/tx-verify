-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Base
public import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_fst00 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ j, d.site = .fst 0 j 0) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  corr_sites s k

theorem stepAt_fst01 (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hs : ∃ j, d.site = .fst 0 j 1) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  corr_sites s k

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
