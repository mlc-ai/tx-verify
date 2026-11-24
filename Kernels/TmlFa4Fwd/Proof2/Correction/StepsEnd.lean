-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Base
public import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_ends (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : (∃ l, d.site = .wend l) ∨ (∃ l, d.site = .barEnd l) ∨ ∃ l, d.site = .exit l) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s except [.barEnd _ => (by corr_issue PTX.Flow.fires_barArrive_next)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
