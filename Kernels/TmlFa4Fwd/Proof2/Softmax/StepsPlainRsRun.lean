-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.StepsPlainRsKinds

@[expose] public section

/-! # Kinds of the plain round's sum

Feed the saved row sum and the accumulator's zero into the add tree. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem rsumPb_ok (hp : Pre p L m) (v : V) : Gen.rsumPb_cond (rbV p v) ∧
    (∀ r, (kOf rbL4 r).Has (lookupD (Gen.rsumPb_facts4 (rbV p v)) r)) := by
  have ha := (rsumPa_ok hp v).2
  rw [rsumPa_keys1] at ha
  have hall : ∀ r, ((Function.update (kOn ((Gen.rsumPa_facts1 fun _ => .pred false).map
      Prod.fst) (kOut (kOf raK) Gen.rsumPa_items0)) 5806 (.s .nn)) r).Has (rbV p v r) := by
    intro r
    by_cases e : r = 5806
    · subst e; rw [Function.update_self]
      show SK.nn.Has (lookupD ((5806, _) :: _) 5806)
      simp only [lookupD, List.lookup, beq_self_eq_true, Option.getD_some]
      exact zero_nn
    · rw [Function.update_of_ne e]
      have hb : (r == 5806) = false := by simpa using e
      have := ha r
      simp only [rbV, lookupD, List.lookup, hb] at this ⊢
      exact this
  have k0 : ∀ r, (kOf rbK r).Has (lookupD (Gen.rsumPb_facts0 (rbV p v)) r) := by
    rw [rsumPb_facts0_eq, rsumPb_keys]
    refine kOf_kList fun r => ?_
    unfold kOn
    split
    · rename_i hr
      rw [lookupD_factsFrom (by simpa using hr)]
      exact hall r
    · trivial
  obtain ⟨hc, hk, -⟩ := rsumPb_chain _ k0
  exact ⟨hc, hk⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
