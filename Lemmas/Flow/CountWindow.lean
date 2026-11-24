-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! # The elements of a list prefix past a count

A proof tool. Among the first `k` positions of a list, those holding an element satisfying `p`
with at least `c` earlier such elements are `count - c` many, `count` the number of such elements
among the first `k` (`card_window`): the positions of the elements satisfying `p` are numbered
by their counts. -/

namespace PTX.Flow

/-- The positions below `k` of elements satisfying `p` with at least `c` earlier ones. -/
theorem card_window {α : Type} (l : List α) (p : α → Bool) (c : Nat) :
    ∀ k, ((Finset.range k).filter fun n =>
      (l[n]?).any p = true ∧ c ≤ (l.take n).countP p).card = (l.take k).countP p - c
  | 0 => by simp
  | k + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, List.take_add_one, List.countP_append]
    cases h : l[k]? with
    | none => simp [card_window l p c k]
    | some x =>
      by_cases hx : p x = true
      · by_cases hk : c ≤ (l.take k).countP p
        · rw [ite_eq_left ⟨by simp [hx], hk⟩, Finset.card_insert_of_notMem (by simp)]
          simp only [Option.toList_some, List.countP_singleton, hx, ↓reduceIte]
          rw [card_window l p c k]
          omega
        · rw [ite_eq_right (by simp [hk])]
          simp only [Option.toList_some, List.countP_singleton, hx, ↓reduceIte]
          rw [card_window l p c k]
          omega
      · rw [ite_eq_right (by simp [hx])]
        simp [hx, card_window l p c k]

end PTX.Flow
