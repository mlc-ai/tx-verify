-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.ExpoBB
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Kernels.TmlFa4Fwd.Flow.Code
import Tactics.KernelRfl

@[expose] public section

/-! # The bias round's exponents: the software path's facts as facts of their values (part 2)

Each run's start and end facts are the facts of their value functions on the run's registers
(literal key lists, written on a dummy value function), so that the instances' pieces, stated on
`factsFrom`, meet the generated runs. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000

theorem expoBB6_facts0_eq (V : Nat → Value) :
    Gen.expoBB6_facts0 V =
      factsFrom ((Gen.expoBB6_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

theorem expoBB7_facts0_eq (V : Nat → Value) :
    Gen.expoBB7_facts0 V =
      factsFrom ((Gen.expoBB7_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

theorem expoBB8_facts0_eq (V : Nat → Value) :
    Gen.expoBB8_facts0 V =
      factsFrom ((Gen.expoBB8_facts0 fun _ => .pred false).map Prod.fst) V := by
  kernel_rfl

theorem expoBB0_end_eq (V : Nat → Value) :
    Gen.expoBB0_facts3 V = factsFrom ((Gen.expoBB0_facts3 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoBB0_facts3 V)) := by
  kernel_rfl

theorem expoBB1_end_eq (V : Nat → Value) :
    Gen.expoBB1_facts1 V = factsFrom ((Gen.expoBB1_facts1 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoBB1_facts1 V)) := by
  kernel_rfl

theorem expoBB2_end_eq (V : Nat → Value) :
    Gen.expoBB2_facts1 V = factsFrom ((Gen.expoBB2_facts1 fun _ => .pred false).map Prod.fst)
      (lookupD (Gen.expoBB2_facts1 V)) := by
  kernel_rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
