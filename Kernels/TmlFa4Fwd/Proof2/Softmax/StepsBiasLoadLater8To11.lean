-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsBiasLoadProof

@[expose] public section

/-! # Final elements of later bias loads 8 to 11 -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bld3_bias_8to11 (hp : Pre p L m) (c : Fin 16) (v : V) (acc : List Value)
    (ha : acc.length = 3) (hlo : 8 ≤ c.val) (hhi : c.val < 12) :
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
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
