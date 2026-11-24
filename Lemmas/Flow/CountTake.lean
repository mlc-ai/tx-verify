-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NthEv

@[expose] public section

/-! # Counts over a segment of a trace

A proof tool. Between two prefixes of a list, a predicate that implies another holds at most as
often as the other (`countP_take_sub_le`): a count of special events cannot grow faster than a
count of the events they are among. An event that does not satisfy the predicate leaves the count
of a thread's prefix unchanged (`countP_take_succ_false`). A count of a disjoint union is the sum
of the counts (`countP_or_disj`), and the remainder of a multiple fixes it (`mul_add_inj`). -/

namespace PTX.Flow

/-- **The growth of a count is at most the growth of a weaker count.** -/
theorem countP_take_sub_le {α : Type} {p q : α → Bool} (hpq : ∀ x, p x = true → q x = true)
    (l : List α) {a b : Nat} (hab : a ≤ b) :
    (l.take b).countP p - (l.take a).countP p ≤ (l.take b).countP q - (l.take a).countP q := by
  have hs : l.take b = l.take a ++ (l.take b).drop a := by
    conv_lhs => rw [← List.take_append_drop a (l.take b)]
    rw [List.take_take, Nat.min_eq_left hab]
  rw [hs, List.countP_append, List.countP_append]
  have := List.countP_mono_left (l := (l.take b).drop a) (fun x _ => hpq x)
  omega

/-- **An event outside the predicate leaves the prefix count unchanged.** -/
theorem countP_take_succ_false {X : Execution} {p : Event → Bool} {g j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hp : p e = false) :
    ((X.tr g).take (j + 1)).countP p = ((X.tr g).take j).countP p := by
  have he' : (X.tr g)[j]? = some e := he
  rw [List.take_add_one, he', Option.toList_some, List.countP_append]
  simp [hp]

/-- **The count of a disjoint union is the sum of the counts.** -/
theorem countP_or_disj {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, ¬ (p x = true ∧ q x = true)) →
      l.countP (fun x => p x || q x) = l.countP p + l.countP q
  | [], _ => by simp
  | a :: l, h => by
    have ih := countP_or_disj (p := p) (q := q) (l := l) (fun x hx => h x (by simp [hx]))
    have ha := h a (by simp)
    simp only [List.countP_cons, ih]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- **A multiple plus a smaller remainder fixes both.** -/
theorem mul_add_inj {a i i' r r' : Nat} (hr : r < a) (hr' : r' < a)
    (h : a * i + r = a * i' + r') : i = i' ∧ r = r' := by
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · have := Nat.mul_le_mul_left a (show i + 1 ≤ i' by omega)
    rw [Nat.mul_add] at this; omega
  · omega
  · have := Nat.mul_le_mul_left a (show i' + 1 ≤ i by omega)
    rw [Nat.mul_add] at this; omega

end PTX.Flow
