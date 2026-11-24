-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CausalObjectWaitCount

@[expose] public section

/-! Selected successful object replies in any window of one object's checked
history equal the thread's successful source waits before a trace position,
provided window membership of this thread's records is exactly `j < k`. -/
namespace PTX
noncomputable section
open AsyncCopy

private theorem countP_take_eq_range {α : Type} (pred : α → Bool) (xs : List α) (k : Nat) :
    (xs.take k).countP pred = (List.range k).countP (fun j => xs[j]?.any pred) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.take_add_one,List.range_succ,List.countP_append,List.countP_append,ih]
    cases hg : xs[k]? <;> simp [hg]

private theorem sourceWaitSuccess_objectAction {X : Execution} {m : Loc} {g j : Nat}
    (hs : (X.get (g,j)).any (sourceWaitSuccess m) = true) :
    ∃ p, objectAction X X.async m (.thread (g,j)) = some (.pollParity p true) := by
  cases he : X.get (g,j) with
  | none => simp only [he,Option.any_none,Bool.false_eq_true] at hs
  | some ev =>
    obtain ⟨pc,kind⟩ := ev
    cases kind <;> try simp only [he,Option.any_some,sourceWaitSuccess,Bool.false_eq_true] at hs
    rename_i target parity ok acquire scope
    cases ok <;> simp only [Bool.false_eq_true,
      decide_eq_true_eq] at hs
    subst hs
    exact ⟨parity,by simp [objectAction,he]⟩

end
end PTX
