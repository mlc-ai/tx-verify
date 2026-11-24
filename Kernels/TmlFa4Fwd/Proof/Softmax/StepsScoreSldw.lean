-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScoreWait0
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScoreWait1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsScoreWait2

@[expose] public section

/-! # The implicit waits of a plain round's first three score loads

`stepAt_sldw`: one file per load (`StepsScoreWait0.lean` and friends), dispatched here. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The implicit waits of a plain round's first three score loads.** -/
theorem stepAt_sldw (hp : Pre p L m) (c : Fin 4) (hc : c.val < 3) (v : V) :
    (codeD p L g).StepAt ⟨.sldw c, v, 1, []⟩ := by
  fin_cases c
  · exact stepAt_sldw_0 hp v
  · exact stepAt_sldw_1 hp v
  · exact stepAt_sldw_2 hp v
  · simp at hc

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
