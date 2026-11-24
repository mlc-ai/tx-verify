-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumStart
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round’s row-sum rescale -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private theorem rsumBa_finite (W : Nat → Value)
    (hW : ∀ q ∈ rsumBaK0, q.2.Has (W q.1)) :
    Gen.rsumBa_cond W ∧
    ∀ r, (kOn ((Gen.rsumBa_facts1 W).map Prod.fst)
      (kOut (kOf rsumBaK0) Gen.rsumBa_items0) r).Has (lookupD (Gen.rsumBa_facts1 W) r) := by
  have k0 : ∀ r, (kOf rsumBaK0 r).Has (lookupD (Gen.rsumBa_facts0 W) r) := by
    rw [rsumBa_facts0_eq]
    exact kstart (by kernel_rfl) hW
  exact kpiece (F := Gen.rsumBa_facts0 W) (G := Gen.rsumBa_facts1 W)
    (items := Gen.rsumBa_items0) (by kernel_rfl) (by kernel_rfl) k0
    (by simp [kFns, XItem.FnOk, Gen.rsumBa_items0])

/-- The rescale's condition and its final register kinds. -/
theorem rsumBa_ok (hp : Pre p L m) (v : V) :
    Gen.rsumBa_cond (lookupD (pBData p L g v)) ∧
    ∀ r, (kOn ((Gen.rsumBa_facts1 (lookupD (pBData p L g v))).map Prod.fst)
      (kOut (kOf rsumBaK0) Gen.rsumBa_items0) r).Has
        (lookupD (Gen.rsumBa_facts1 (lookupD (pBData p L g v))) r) :=
  rsumBa_finite _ (pB_sumKind hp v)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
