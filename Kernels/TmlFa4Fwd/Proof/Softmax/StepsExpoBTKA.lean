-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTA
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's exponents: the tail's conditions and kinds after the hardware path

From the values of the named-barrier arrival: the hardware path's end kinds give the tail's first
run its start kinds, the unpack at pc 6380 gives the second run's (the low half is the path's
register `%r3607`, whose term the pair's term contains), and the two runs' kind chains give their
conditions and the stretch's end kinds (`tailA_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The tail's first run's start values after the hardware path. -/
abbrev vTA (p : Params) (L : Launch) (g : Nat) (v : V) : Nat → Value :=
  lookupD (Gen.expoBA_facts5 (vExpoB p L g v))

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The tail after the hardware path.** -/
theorem tailA_ok (hp : Pre p L m) (v : V) :
    Gen.expoBTA0_cond (vTA p L g v) ∧
      (∀ r, (kOf tAa3 r).Has (lookupD (Gen.expoBTA0_facts3 (vTA p L g v)) r)) ∧
      Gen.expoBTA1_cond (nextTA (vTA p L g v)) ∧
      ∀ r, (kOf tAb4 r).Has (lookupD (Gen.expoBTA1_facts4 (nextTA (vTA p L g v))) r) := by
  have k0 : ∀ r, (kOf tAK0 r).Has (lookupD (Gen.expoBTA0_facts0 (vTA p L g v)) r) := by
    rw [expoBTA0_facts0_eq]
    exact kstart (by unfold tAK0; kernel_rfl) fun q hq => by
      rw [mem_kList hq]; exact (expoBA_ok (g := g) hp v).2 q.1
  have c0 := expoBTA0_chain _ k0
  have k1 : ∀ r, (kOf tAK1 r).Has (lookupD (Gen.expoBTA1_facts0 (nextTA (vTA p L g v))) r) := by
    rw [expoBTA1_facts0_eq]
    refine kstart (by unfold tAK1; kernel_rfl) fun q hq => ?_
    rw [mem_kList hq]
    by_cases e : q.1 = 4905
    · rw [e]
      simp only [beq_self_eq_true, ↓reduceIte, nextTA, Function.update_self]
      have hj : lookupD (Gen.expoBTA0_facts3 (vTA p L g v)) 9556 =
          joinValue (lookupD (Gen.expoBTA0_facts3 (vTA p L g v)) 4667) (vExpoB p L g v 1458) := by
        kernel_rfl
      rw [hj, split_join_lo (clean_of_isS (c0.2 4667) (by kernel_rfl))]
      exact c0.2 4667
    · have hb : (q.1 == 4905) = false := by simpa using e
      simp only [hb, Bool.false_eq_true, ↓reduceIte, nextTA]
      rw [Function.update_of_ne e]
      exact c0.2 q.1
  have c1 := expoBTA1_chain _ k1
  exact ⟨c0.1, c0.2, c1.1, c1.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
