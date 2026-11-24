-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Correction.Loads
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

theorem stepAt_rld (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : (∃ st c, d.site = .rld st c) ∨ ∃ st c, d.site = .rst st c) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s except [.rld _ _ => (by corr_rld), .rst _ _ => (by corr_tst)]

theorem stepAt_rldw (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 1)
    (hs : ∃ st c, d.site = .rldw st c) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s except [.rldw _ _ => (by corr_rldw)]

/-- The implicit wait's site at sub-step 0 is not a state the machine reaches; it stops. -/
theorem stepAt_rldw0 (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : ∃ st c, d.site = .rldw st c) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Correction
