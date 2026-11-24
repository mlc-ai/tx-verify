-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.MBarrierHistory
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Count

@[expose] public section

/-! # Counting events by the records they leave

A proof tool. If each event of a list that satisfies `p` leaves a record satisfying `q` in a log
whose record identities are distinct, and distinct events leave records of distinct identities,
the log has at least as many such records as the list has such events
(`countP_le_of_records`). -/

namespace PTX.MBarrier

/-- The indices of a list whose element satisfies `p`. -/
def indicesP {α : Type} (p : α → Bool) (es : List α) : Finset Nat :=
  (Finset.range es.length).filter (fun i => (es[i]?.map p).getD false)

theorem countP_eq_card {α : Type} (p : α → Bool) (es : List α) :
    es.countP p = (indicesP p es).card := by
  induction es using List.reverseRecOn with
  | nil => simp [indicesP]
  | append_singleton es e ih =>
    have hset : indicesP p (es ++ [e]) =
        if p e then insert es.length (indicesP p es) else indicesP p es := by
      ext i
      simp only [indicesP, Finset.mem_filter, Finset.mem_range, List.length_append,
        List.length_singleton]
      by_cases hi : i < es.length
      · rw [List.getElem?_append_left hi]
        split_ifs with hp
        · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨-, h⟩; exact .inr ⟨hi, h⟩
          · rintro (rfl | ⟨-, h⟩)
            · omega
            · exact ⟨by omega, h⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨fun ⟨_, h⟩ => ⟨hi, h⟩, fun ⟨_, h⟩ => ⟨by omega, h⟩⟩
      · by_cases he : i = es.length
        · subst he
          simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.map_some, Option.getD_some]
          split_ifs with hp
          · simp [hp]
          · simp only [Finset.mem_filter, Finset.mem_range]
            simp [hp]
        · have hge : es.length + 1 ≤ i ∨ i < es.length := by omega
          rcases hge with hge | hlt
          · constructor
            · rintro ⟨h, -⟩; omega
            · intro h
              split_ifs at h
              · rcases Finset.mem_insert.mp h with h | h
                · omega
                · simp only [Finset.mem_filter, Finset.mem_range] at h; omega
              · simp only [Finset.mem_filter, Finset.mem_range] at h; omega
          · omega
    rw [List.countP_append, ih, hset]
    split_ifs with hp
    · rw [Finset.card_insert_of_notMem]
      · simp [hp]
      · simp [indicesP]
    · simp [hp]

/-- Events that each leave a distinct record satisfying `q` are at most the records satisfying
`q`. -/
theorem countP_le_of_records {α ι : Type} [DecidableEq ι] {p : α → Bool} {es : List α}
    {q : Record ι → Bool} {log : List (Record ι)} (f : Nat → ι)
    (hf : ∀ i j, i ∈ indicesP p es → j ∈ indicesP p es → f i = f j → i = j)
    (hmem : ∀ i, i ∈ indicesP p es → ∃ r ∈ log, r.id = f i ∧ q r = true) :
    es.countP p ≤ log.countP q := by
  rw [countP_eq_card]
  calc (indicesP p es).card ≤ ((log.filter q).map Record.id).toFinset.card := by
        apply Finset.card_le_card_of_injOn f
        · intro i hi
          obtain ⟨r, hr, hid, hq⟩ := hmem i hi
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_filter]
          exact ⟨r, ⟨hr, hq⟩, hid⟩
        · intro i hi j hj h
          exact hf i j hi hj h
    _ ≤ ((log.filter q).map Record.id).length := List.toFinset_card_le _
    _ = log.countP q := by simp [List.countP_eq_length_filter]

end PTX.MBarrier
