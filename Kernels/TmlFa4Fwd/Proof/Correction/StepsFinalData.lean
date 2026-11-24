-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Correction.Base
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepCorrection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_fld (hp : Pre p L m) (_hg : g < L.threads) (d : D) (hk : d.k = 0)
    (hs : (∃ st j, d.site = .fld st j) ∨ ∃ st j, d.site = .fwl st j) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k⟩ := d
  cases hk
  corr_sites s except [.fld _ _ => (by corr_fld)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
