-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Counting entries of a list's prefixes

A proof tool for counts of a thread's events. When every entry of a list that `p` selects is
selected by exactly one of `q` and `r`, the count of `p` is the sum of the counts of `q` and `r`
(`countP_split`). When a prefix of a list has an entry `p` selects, its first such entry has no
earlier one (`first_countP`). -/

namespace PTX.Flow

/-- **A count splits** along a disjoint cover of the selected entries. -/
theorem countP_split {α : Type} {p q r : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = (q x || r x)) (hd : ∀ x ∈ l, ¬ (q x = true ∧ r x = true)) :
    l.countP p = l.countP q + l.countP r := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have hdx := hd x (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
        (fun y hy => hd y (List.mem_cons_of_mem _ hy)), hx]
    cases hq : q x <;> cases hr : r x <;> simp only [hq, hr] at hdx ⊢ <;> simp at hdx ⊢ <;>
      omega

/-- **The first selected entry of a prefix**: when the first `k` entries hold one that `p`
selects, the first of them has no selected entry before it. -/
theorem first_countP {α : Type} {p : α → Bool} {l : List α} {k : Nat}
    (h : 0 < (l.take k).countP p) :
    ∃ b < k, ∃ x, l[b]? = some x ∧ p x = true ∧ (l.take b).countP p = 0 := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    by_cases h0 : 0 < (l.take k).countP p
    · obtain ⟨b, hb, x, hx, hp, hc⟩ := ih h0
      exact ⟨b, by omega, x, hx, hp, hc⟩
    · have hk : k < l.length := by
        by_contra hl
        rw [List.take_of_length_le (by omega)] at h
        rw [List.take_of_length_le (by omega)] at h0
        exact h0 h
      have ht : l.take (k + 1) = l.take k ++ [l[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      rw [ht, List.countP_append] at h
      refine ⟨k, by omega, l[k], List.getElem?_eq_getElem hk, ?_, by omega⟩
      by_contra hp
      exact h0 (by simpa [hp] using h)

/-- **The entry of a prefix with `n` selected entries before it**: when the first `k` entries
hold more than `n` that `p` selects, one of them has exactly `n` before it. -/
theorem nth_countP {α : Type} {p : α → Bool} {l : List α} {k n : Nat}
    (h : n < (l.take k).countP p) :
    ∃ b < k, ∃ x, l[b]? = some x ∧ p x = true ∧ (l.take b).countP p = n := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    by_cases h0 : n < (l.take k).countP p
    · obtain ⟨b, hb, x, hx, hp, hc⟩ := ih h0
      exact ⟨b, by omega, x, hx, hp, hc⟩
    · have hk : k < l.length := by
        by_contra hl
        rw [List.take_of_length_le (by omega)] at h
        rw [List.take_of_length_le (by omega)] at h0
        exact h0 h
      have ht : l.take (k + 1) = l.take k ++ [l[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      rw [ht, List.countP_append] at h
      cases hp : p l[k]
      · simp [hp] at h; omega
      · simp only [hp, List.countP_singleton, ite_true] at h
        exact ⟨k, by omega, l[k], List.getElem?_eq_getElem hk, hp, by omega⟩

end PTX.Flow
