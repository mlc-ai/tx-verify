-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoadFirst0To3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoadFirst12To15
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoadFirst4To7
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasLoadFirst8To11

@[expose] public section

/-! # The last element of each first bias load -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem stepAt_bld3_first (hp : Pre p L m) (c : Fin 16) (v : V) (acc : List Value)
    (ha : acc.length = 3) : (codeD p L g).StepAt ⟨.bld false c, v, 3, acc⟩ := by
  by_cases h4 : c.val < 4
  · exact stepAt_bld3_first_0to3 hp c v acc ha (Nat.zero_le _) h4
  by_cases h8 : c.val < 8
  · exact stepAt_bld3_first_4to7 hp c v acc ha (Nat.le_of_not_gt h4) h8
  by_cases h12 : c.val < 12
  · exact stepAt_bld3_first_8to11 hp c v acc ha (Nat.le_of_not_gt h8) h12
  · exact stepAt_bld3_first_12to15 hp c v acc ha (Nat.le_of_not_gt h12) c.isLt


end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
