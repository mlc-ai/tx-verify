-- SPDX-License-Identifier: Apache-2.0
module

import Mathlib.Data.List.Infix

@[expose] public section

/-! # The positions of a counted predicate

The `m`-th element of a list satisfying `p` (counting from `0`) exists below the count
(`exists_countP_eq`) and the prefix count at a later position is larger (`countP_take_lt_at`). -/

namespace PTX.Kit

/-- **The `m`-th element satisfying `p`**: below the count, an element at a position whose
prefix count is `m`. -/
theorem exists_countP_eq {α : Type} (p : α → Bool) :
    ∀ (l : List α) (m : Nat), m < l.countP p →
      ∃ k x, l[k]? = some x ∧ p x = true ∧ (l.take k).countP p = m
  | [], m, h => by simp at h
  | x :: xs, m, h => by
    by_cases hx : p x = true
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact ⟨0, x, rfl, hx, by simp⟩
      · rw [List.countP_cons_of_pos hx] at h
        obtain ⟨k, y, h1, h2, h3⟩ := exists_countP_eq p xs (m - 1) (by omega)
        exact ⟨k + 1, y, h1, h2, by
          rw [List.take_succ_cons, List.countP_cons_of_pos hx, h3]; omega⟩
    · rw [List.countP_cons_of_neg (by simpa using hx)] at h
      obtain ⟨k, y, h1, h2, h3⟩ := exists_countP_eq p xs m h
      exact ⟨k + 1, y, h1, h2, by
        rw [List.take_succ_cons, List.countP_cons_of_neg (by simpa using hx), h3]⟩

/-- A satisfying element at `k` makes the prefix count at a later position larger. -/
theorem countP_take_lt_at {α : Type} (p : α → Bool) {l : List α} {k k' : Nat} {x : α}
    (hk : k < k') (hx : l[k]? = some x) (hp : p x = true) :
    (l.take k).countP p < (l.take k').countP p := by
  have h1 : (l.take (k + 1)).countP p = (l.take k).countP p + 1 := by
    rw [List.take_add_one, hx]; simp [List.countP_append, hp]
  have h2 : (l.take (k + 1)).countP p ≤ (l.take k').countP p :=
    (List.take_isPrefix_take.mpr (Or.inl (by omega))).countP_le
  omega

end PTX.Kit
