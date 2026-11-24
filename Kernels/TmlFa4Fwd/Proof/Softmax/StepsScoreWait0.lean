-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Gen.StepSoftmax.Part008
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScoreLib
import Lemmas.Flow.Step.TcSteps
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # One implicit wait of a plain round's score load

The implicit wait of the plain round's score load 0 (sub-step 1: the packs of the loaded
registers, to the next load), its own file so that the round's waits check in parallel; the
family theorem is `stepAt_sldw`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_sldw_0 (hp : Pre p L m) (v : V) :
    (codeD p L g).StepAt ⟨.sldw 0, v, 1, []⟩ := by
  have hparams := params hp
  soft_sldw

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
