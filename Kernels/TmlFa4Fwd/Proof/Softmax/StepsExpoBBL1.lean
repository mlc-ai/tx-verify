-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The bias round's exponents: the lane kinds of the software `exp2` instances, part 1

The two lane inputs of each instance have a kind at most `ni` after the run before it. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000

/-- A kind at most `ni`. -/
def kLeNi : Kd → Bool
  | .s s => s.le .ni
  | _ => false

theorem ni_of_kLeNi {k : Kd} {v : Value} (h : k.Has v) (hk : kLeNi k = true) : SK.ni.Has v := by
  cases k with
  | s s => exact SK.mono hk h
  | _ => simp [kLeNi] at hk

theorem laneK0 : kLeNi (kOf bB0_3 1407) = true ∧
    kLeNi (kOf bB0_3 1408) = true := by decide +kernel

theorem laneK1 : kLeNi (kOf bB1_1 1409) = true ∧
    kLeNi (kOf bB1_1 1410) = true := by decide +kernel

theorem laneK2 : kLeNi (kOf bB2_1 1423) = true ∧
    kLeNi (kOf bB2_1 1424) = true := by decide +kernel

theorem laneK3 : kLeNi (kOf bB3_1 1425) = true ∧
    kLeNi (kOf bB3_1 1426) = true := by decide +kernel

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
