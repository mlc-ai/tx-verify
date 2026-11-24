-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Open
import Kernels.TmlFa4Fwd.Proof.Softmax.Steps

@[expose] public section

/-! # The step obligation of the softmax warps, from the numeric steps -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The step obligation at every state, from the numeric steps. -/
theorem stepAt (hp : Pre p L m) (hg : g < L.threads) (hw : g % L.block / 32 < 8)
    (hN : NumSteps p L g) (d : D) : (codeD p L g).StepAt d := by
  cases hn : d.numeric
  · exact stepAt_ctl hp hg hw d hn
  · exact hN d hn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
