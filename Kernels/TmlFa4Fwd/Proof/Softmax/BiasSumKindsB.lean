-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumKinds
import Tactics.KernelRfl

@[expose] public section

/-! # Bias row-sum kinds at the end of exponent path B -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem sumStartKB :
    rsumBaKeys.all (fun r => r == 1362 || r == 7257 || checkSumKind (kOf tBb4) r) = true := by
  kernel_rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
