-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Lemmas.Flow.Step.TcSteps
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # A bias round's P part: the control sites on the control machine

`StepsBiasP.lean` lifts them to the data machine. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The control sites of a bias round's P part, on the control machine. -/
theorem stepAt_bias_pctl (hp : Pre p L m) (_hg : g < L.threads) (d : D)
    (hk : d.k = 0) (ha : d.acc = [])
    (hs : d.site = .pst .bias 2 ∨ d.site = .pwst .bias 0 ∨ d.site = .pst .bias 3 ∨
      d.site = .pwst .bias 1 ∨ d.site = .pws .bias ∨ d.site = .pel .bias ∨
      d.site = .parr2 .bias) :
    (code p L g).StepAt d := by
  have hparams := params hp
  obtain ⟨s, v, k, acc⟩ := d
  cases hk; cases ha
  soft_sites s except [.pst _ _ => (by soft_tst)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
