-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.BiasSumTreeKinds
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs2
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bias round's sum tree -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

private abbrev bbStart (W : Nat → Value) : Nat → Value :=
  lookupD ((5123, .bits 32 0) :: Gen.rsumBa_facts1 W)

private theorem rsumBb_ready (W : Nat → Value)
    (ha : ∀ r, (kOn ((Gen.rsumBa_facts1 W).map Prod.fst)
      (kOut (kOf rsumBaK0) Gen.rsumBa_items0) r).Has (lookupD (Gen.rsumBa_facts1 W) r)) :
    Gen.rsumBb_cond (bbStart W) ∧
      ∀ r, (kOf rsumBbK3 r).Has (lookupD (Gen.rsumBb_facts3 (bbStart W)) r) := by
  have hKinds := ha
  rw [rsumBa_keys1] at hKinds
  have hall : ∀ r, ((Function.update (kOn ((Gen.rsumBa_facts1 fun _ => .pred false).map
      Prod.fst) (kOut (kOf rsumBaK0) Gen.rsumBa_items0)) 5123 (.s .nn)) r).Has
        (bbStart W r) := by
    intro r
    by_cases e : r = 5123
    · subst e; rw [Function.update_self]
      show SK.nn.Has (lookupD ((5123, _) :: _) 5123)
      simp only [lookupD, List.lookup, beq_self_eq_true, Option.getD_some]
      exact zero_nn
    · rw [Function.update_of_ne e]
      have hb : (r == 5123) = false := by simpa using e
      have := hKinds r
      simp only [bbStart, lookupD, List.lookup, hb] at this ⊢
      exact this
  have k0 : ∀ r, (kOf rsumBbK0 r).Has (lookupD (Gen.rsumBb_facts0 (bbStart W)) r) := by
    rw [rsumBb_facts0_eq, rsumBb_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  exact rsumBb_chain _ k0

theorem rsumBb_ok (hp : Pre p L m) (v : V) : Gen.rsumBb_cond (rsumBbStart p L g v) ∧
    (∀ r, (kOf rsumBbK3 r).Has (lookupD (Gen.rsumBb_facts3 (rsumBbStart p L g v)) r)) :=
  rsumBb_ready _ (rsumBa_ok (g := g) hp v).2

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
