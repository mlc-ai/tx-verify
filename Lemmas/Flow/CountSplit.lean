-- SPDX-License-Identifier: Apache-2.0
module

public import Init.Omega

@[expose] public section

/-! # Counting by exclusive cases

A proof tool. When every entry of a list that a predicate selects is selected by exactly one of
three exclusive predicates, and those are selected only by it, the count splits into the three
counts (`countP_split3`). -/

namespace PTX.Flow

theorem countP_split3 {α : Type} {p q1 q2 q3 : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, (if p x then 1 else 0) =
      (if q1 x then 1 else 0) + (if q2 x then 1 else 0) + (if q3 x then 1 else 0)) →
      l.countP p = l.countP q1 + l.countP q2 + l.countP q3
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := countP_split3 (l := l) fun x hx => h x (List.mem_cons_of_mem a hx)
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    omega

end PTX.Flow
