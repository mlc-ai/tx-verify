-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup

@[expose] public section

/-! # Counting entries of a list

Generic list facts used by the ring protocols: the `c`-th entry satisfying a predicate
(`exists_nth_countP`), a prefix count as a finset of positions (`countP_take_card`), and the
pigeonhole bounds `length_le_card_of_rel` and `length_le_countP_take`. -/

namespace PTX.MbarRing.Slot

noncomputable section

/-- A list with more than `c` entries satisfying `P` has its `c`-th such entry somewhere. -/
theorem exists_nth_countP {α : Type} (P : α → Bool) :
    ∀ {xs : List α} {c : Nat}, c + 1 ≤ xs.countP P →
      ∃ j x, xs[j]? = some x ∧ P x = true ∧ (xs.take j).countP P = c
  | [], c, h => by simp at h
  | x :: xs, c, h => by
    by_cases hx : P x = true
    · rcases c with _ | c
      · exact ⟨0, x, rfl, hx, by simp⟩
      · rw [List.countP_cons_of_pos hx] at h
        obtain ⟨j, y, hy, hp, hc⟩ := exists_nth_countP P (xs := xs) (c := c) (by omega)
        exact ⟨j + 1, y, by simpa using hy, hp, by simp [List.countP_cons_of_pos hx, hc]⟩
    · rw [List.countP_cons_of_neg hx] at h
      obtain ⟨j, y, hy, hp, hc⟩ := exists_nth_countP P (xs := xs) (c := c) h
      exact ⟨j + 1, y, by simpa using hy, hp, by simp [List.countP_cons_of_neg hx, hc]⟩

/-- A list without repetitions whose elements are each related to an element of a finset, the
relation being injective on that finset, is no longer than the finset. -/
theorem length_le_card_of_rel {α β : Type} [DecidableEq α] (xs : List α)
    (hxs : xs.Nodup) (t : Finset β) (R : α → β → Prop)
    (hex : ∀ x ∈ xs, ∃ y ∈ t, R x y)
    (huniq : ∀ x ∈ xs, ∀ x' ∈ xs, ∀ y ∈ t, R x y → R x' y → x = x') :
    xs.length ≤ t.card := by
  cases xs with
  | nil => simp
  | cons x0 rest =>
    obtain ⟨y0, hy0, -⟩ := hex x0 (by simp)
    have hchoice : ∀ x : α, ∃ y : β, x ∈ x0 :: rest → y ∈ t ∧ R x y := by
      intro x
      by_cases hx : x ∈ x0 :: rest
      · obtain ⟨y, hy, hR⟩ := hex x hx
        exact ⟨y, fun _ => ⟨hy, hR⟩⟩
      · exact ⟨y0, fun h => absurd h hx⟩
    choose f hf using hchoice
    have hcard : (x0 :: rest).toFinset.card ≤ t.card := by
      apply Finset.card_le_card_of_injOn f
      · intro x hx
        exact Finset.mem_coe.mpr (hf x (List.mem_toFinset.mp (Finset.mem_coe.mp hx))).1
      · intro x hx x' hx' hfxx'
        have hx1 := List.mem_toFinset.mp (Finset.mem_coe.mp hx)
        have hx1' := List.mem_toFinset.mp (Finset.mem_coe.mp hx')
        have h1 := (hf x hx1).2
        have h2 := (hf x' hx1').2
        rw [hfxx'] at h1
        exact huniq x hx1 x' hx1' (f x') (hf x' hx1').1 h1 h2
    rw [List.toFinset_card_of_nodup hxs] at hcard
    exact hcard

/-- The entries of a list's prefix that satisfy `p`, as positions. -/
theorem countP_take_card {β : Type} (es : List β) (p : β → Bool) :
    ∀ K, (es.take K).countP p = ((Finset.range K).filter (fun j => (es[j]?).any p = true)).card
  | 0 => by simp
  | K + 1 => by
    rw [Finset.range_add_one, Finset.filter_insert, List.take_add_one, List.countP_append,
      countP_take_card es p K]
    cases h : es[K]? with
    | none => simp
    | some x =>
      by_cases hx : p x = true
      · rw [ite_eq_left (by simp [hx]), Finset.card_insert_of_notMem (by simp)]
        simp [hx]
      · rw [ite_eq_right (by simp [hx])]
        simp [hx]

/-- A list without repetitions whose entries name distinct positions below `K` of entries of
`es` satisfying `p` is no longer than the count of such entries among the first `K`. -/
theorem length_le_countP_take {α β : Type} [DecidableEq α] (xs : List α) (hxs : xs.Nodup)
    (es : List β) (p : β → Bool) (K : Nat) (f : α → Nat)
    (hf : ∀ x ∈ xs, f x < K ∧ (es[f x]?).any p = true)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : xs.length ≤ (es.take K).countP p := by
  rw [countP_take_card]
  refine length_le_card_of_rel xs hxs _ (fun x j => f x = j) (fun x hx => ⟨f x, ?_, rfl⟩) ?_
  · simp only [Finset.mem_filter, Finset.mem_range]
    exact hf x hx
  · intro x hx y hy j _ h1 h2
    exact hinj x hx y hy (h1.trans h2.symm)

end

end PTX.MbarRing.Slot
