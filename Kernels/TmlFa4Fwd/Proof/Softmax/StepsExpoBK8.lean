-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK2
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBSeg
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS4
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBI
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's exponents: the software path's kinds from the arrival's values

The software path's start kinds from the scaled-product run's end kinds (`bb0_k0`), and the end
kinds of its last run (`bb8_kinds`), for the tail and the P part. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem bb0_k0 (hp : Pre p L m) (v : V) :
    ∀ r, (kOf bK0 r).Has (lookupD (Gen.expoBB0_facts0 (vExpoB p L g v)) r) := by
  rw [expoBB0_facts0_eq]
  exact kstart (by unfold bK0; kernel_rfl) fun q hq => by
    rw [mem_kList hq]; exact (expoB0_ok (g := g) hp v).2 q.1

/-- **The software path's end kinds.** -/
theorem bb8_kinds (hp : Pre p L m) (v : V) :
    ∀ r, (kOf bB8_1 r).Has (lookupD (Gen.expoBB8_facts1 (vB8 (vExpoB p L g v))) r) := by
  have e0 := expoBB0_chain (vB0 (vExpoB p L g v)) (bb0_k0 hp v)
  have e1 := expoBB1_chain (vB1 (vExpoB p L g v)) (k0_1 _ e0.2)
  have e2 := expoBB2_chain (vB2 (vExpoB p L g v)) (k0_2 _ e1.2)
  have e3 := expoBB3_chain (vB3 (vExpoB p L g v)) (k0_3 _ e2.2)
  have e4 := expoBB4_chain (vB4 (vExpoB p L g v)) (k0_4 _ e3.2)
  have e5 := expoBB5_chain (vB5 (vExpoB p L g v)) (k0_5 _ e4.2)
  have e6 := expoBB6_chain (vB6 (vExpoB p L g v)) (k0_6 _ e5.2)
  have e7 := expoBB7_chain (vB7 (vExpoB p L g v)) (k0_7 _ e6.2)
  have e8 := expoBB8_chain (vB8 (vExpoB p L g v)) (k0_8 _ e7.2)
  exact e8.2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
