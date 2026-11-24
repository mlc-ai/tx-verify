-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK2
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBL1
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The bias round's exponents: the lane kinds of the software `exp2` instances, part 2

The two lane inputs of each instance have a kind at most `ni` after the run before it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000

theorem laneK4 : kLeNi (kOf bB4_1 1439) = true ∧
    kLeNi (kOf bB4_1 1440) = true := by decide +kernel

theorem laneK5 : kLeNi (kOf bB5_1 1441) = true ∧
    kLeNi (kOf bB5_1 1442) = true := by decide +kernel

theorem laneK6 : kLeNi (kOf bB6_1 1455) = true ∧
    kLeNi (kOf bB6_1 1456) = true := by decide +kernel

theorem laneK7 : kLeNi (kOf bB7_1 1457) = true ∧
    kLeNi (kOf bB7_1 1458) = true := by decide +kernel

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
