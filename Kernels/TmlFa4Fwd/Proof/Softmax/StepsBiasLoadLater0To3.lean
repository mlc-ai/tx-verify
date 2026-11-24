-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasUnpack
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoadProof
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Final elements of later bias loads 0 to 3 -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bld3_bias_0to3 (hp : Pre p L m) (c : Fin 16) (v : V) (acc : List Value)
    (ha : acc.length = 3) (hlo : 0 ≤ c.val) (hhi : c.val < 4) :
    (codeD p L g).StepAt ⟨.bld true c, v, 3, acc⟩ := by
  have hparams := params hp
  match acc, ha with
  | [a0, a1, a2], _ =>
    fin_cases c
    all_goals first
      | (norm_num at hlo; done)
      | (norm_num at hhi; done)
      | soft_bld3

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
