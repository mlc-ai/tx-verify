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

theorem stepAt_final (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : d.site = .farr0 ∨ (∃ st, d.site = .fbar st) ∨ (∃ st, d.site = .fsum st) ∨
      (∃ st, d.site = .fmax st) ∨ (∃ st, d.site = .farr st) ∨ (∃ st k, d.site = .fw st k) ∨
      (∃ st, d.site = .fence st) ∨
      d.site = .fdone 0 0 ∨ d.site = .fdone 0 1 ∨ d.site = .fdone 1 0) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
