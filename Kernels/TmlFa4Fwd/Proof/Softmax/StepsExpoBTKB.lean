-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTB
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's exponents: the tail's conditions and kinds after the software path

From the values of the named-barrier arrival: the software path's end kinds give the tail's first
run its start kinds, the unpack at pc 6380 gives the second run's (the low half is the path's
register `%r3650`, whose term the pair's term contains), and the two runs' kind chains give their
conditions and the stretch's end kinds (`tailB_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The tail's first run's start values after the software path. -/
abbrev vTB (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  lookupD (Gen.expoBB8_facts1 (vB8 (vExpoB p L g v)))

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private theorem tailB_join (W : Nat → Value) :
    let U := lookupD (Gen.expoBB8_facts1 W)
    lookupD (Gen.expoBTB0_facts3 U) 9556 =
      joinValue (lookupD (Gen.expoBTB0_facts3 U) 4710) (W 1458) := by
  kernel_rfl

/-- **The tail after the software path.** -/
theorem tailB_ok (v : V)
    (hB : ∀ r, (kOf bB8_1 r).Has (vTB p L g v r)) :
    Gen.expoBTB0_cond (vTB p L g v) ∧
      (∀ r, (kOf tBa3 r).Has (lookupD (Gen.expoBTB0_facts3 (vTB p L g v)) r)) ∧
      Gen.expoBTB1_cond (nextTB (vTB p L g v)) ∧
      ∀ r, (kOf tBb4 r).Has (lookupD (Gen.expoBTB1_facts4 (nextTB (vTB p L g v))) r) := by
  have k0 : ∀ r, (kOf tBK0 r).Has (lookupD (Gen.expoBTB0_facts0 (vTB p L g v)) r) := by
    rw [expoBTB0_facts0_eq]
    exact kstart (by unfold tBK0; kernel_rfl) fun q hq => by
      rw [mem_kList hq]; exact hB q.1
  have c0 := expoBTB0_chain _ k0
  have k1 : ∀ r, (kOf tBK1 r).Has (lookupD (Gen.expoBTB1_facts0 (nextTB (vTB p L g v))) r) := by
    rw [expoBTB1_facts0_eq]
    refine kstart (by unfold tBK1; kernel_rfl) fun q hq => ?_
    rw [mem_kList hq]
    by_cases e : q.1 = 4905
    · rw [e]
      simp only [beq_self_eq_true, ↓reduceIte, nextTB, Function.update_self]
      have hj : lookupD (Gen.expoBTB0_facts3 (vTB p L g v)) 9556 =
          joinValue (lookupD (Gen.expoBTB0_facts3 (vTB p L g v)) 4710)
            (vB8 (vExpoB p L g v) 1458) :=
        tailB_join (vB8 (vExpoB p L g v))
      rw [hj, split_join_lo (clean_of_isS (c0.2 4710) (by kernel_rfl))]
      exact c0.2 4710
    · have hb : (q.1 == 4905) = false := by simpa using e
      simp only [hb, Bool.false_eq_true, ↓reduceIte, nextTB]
      rw [Function.update_of_ne e]
      exact c0.2 q.1
  have c1 := expoBTB1_chain _ k1
  exact ⟨c0.1, c0.2, c1.1, c1.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
