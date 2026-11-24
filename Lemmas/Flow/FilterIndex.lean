-- SPDX-License-Identifier: Apache-2.0
module

public import Init.Data.List.Lemmas

@[expose] public section

/-! # The position of an entry among the selected entries

A proof tool. An entry a predicate selects is the selected entry numbered by the selected
entries before it (`filter_getElem_countP`), and the selected entries of a prefix keep their
numbers in a longer list (`filter_append_getElem`). -/

namespace PTX.Flow

theorem filter_getElem_countP {α : Type} {p : α → Bool} :
    ∀ {l : List α} {k : Nat} {x : α}, l[k]? = some x → p x = true →
      (l.filter p)[(l.take k).countP p]? = some x
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, x, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hp]
  | a :: l, k + 1, x, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    have ih := filter_getElem_countP h hp
    by_cases ha : p a = true
    · simp only [List.filter_cons, ha, ↓reduceIte, List.take_succ_cons, List.countP_cons,
        List.getElem?_cons_succ]
      exact ih
    · simp only [List.filter_cons, ha, Bool.false_eq_true, ↓reduceIte, List.take_succ_cons,
        List.countP_cons, Nat.add_zero]
      exact ih

theorem filter_append_getElem {α : Type} {p : α → Bool} {l l' : List α} {o : Nat}
    (h : o < l.countP p) : ((l ++ l').filter p)[o]? = (l.filter p)[o]? := by
  rw [List.filter_append, List.getElem?_append_left]
  rw [← List.countP_eq_length_filter]
  exact h

end PTX.Flow
