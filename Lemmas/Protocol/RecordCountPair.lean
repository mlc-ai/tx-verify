-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RecordCount

@[expose] public section

/-! # Counting the events of two lists by the records they leave

The two-list form of `countP_le_of_records`. Events of two lists each leave a record of a log,
whose identities are distinct within each list and across the two lists. Then the events of
both lists satisfying `p` are at most the records satisfying `q` (`countP_le_of_records_pair`).
The proof concatenates the lists and applies the one-list lemma. -/

namespace PTX.MBarrier

/-- The indices of a list whose element satisfies `p`, read off the element. -/
theorem mem_indicesP_iff {α : Type} (p : α → Bool) (es : List α) (i : Nat) :
    i ∈ indicesP p es ↔ ∃ e, es[i]? = some e ∧ p e = true := by
  unfold indicesP
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩
    cases he : es[i]? with
    | none => simp [he] at h
    | some e => exact ⟨e, rfl, by simpa [he] using h⟩
  · rintro ⟨e, he, hp⟩
    have hi : i < es.length := by
      rcases Nat.lt_or_ge i es.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at he
        cases he
    exact ⟨hi, by simp [he, hp]⟩

/-- The indices of a concatenation: those of the first list, then those of the second, shifted. -/
theorem mem_indicesP_append {α : Type} (p : α → Bool) (es₁ es₂ : List α) (i : Nat) :
    i ∈ indicesP p (es₁ ++ es₂) ↔
      (i < es₁.length ∧ i ∈ indicesP p es₁) ∨
        (es₁.length ≤ i ∧ i - es₁.length ∈ indicesP p es₂) := by
  simp only [mem_indicesP_iff]
  constructor
  · rintro ⟨e, he, hp⟩
    by_cases hi : i < es₁.length
    · left
      exact ⟨hi, e, by rwa [List.getElem?_append_left hi] at he, hp⟩
    · right
      refine ⟨by omega, e, ?_, hp⟩
      rw [List.getElem?_append_right (by omega)] at he
      exact he
  · rintro (⟨hi, e, he, hp⟩ | ⟨hi, e, he, hp⟩)
    · exact ⟨e, by rw [List.getElem?_append_left hi]; exact he, hp⟩
    · exact ⟨e, by rw [List.getElem?_append_right hi]; exact he, hp⟩

/-- Events of two lists that each leave a record satisfying `q`, with record identities injective
within each list and disjoint across the two lists, are at most the records satisfying `q`. -/
theorem countP_le_of_records_pair {α ι : Type} [DecidableEq ι] {p : α → Bool}
    {es₁ es₂ : List α} {q : Record ι → Bool} {log : List (Record ι)}
    (f₁ f₂ : Nat → ι)
    (hf₁ : ∀ i j, i ∈ indicesP p es₁ → j ∈ indicesP p es₁ → f₁ i = f₁ j → i = j)
    (hf₂ : ∀ i j, i ∈ indicesP p es₂ → j ∈ indicesP p es₂ → f₂ i = f₂ j → i = j)
    (hdisj : ∀ i j, i ∈ indicesP p es₁ → j ∈ indicesP p es₂ → f₁ i ≠ f₂ j)
    (hmem₁ : ∀ i, i ∈ indicesP p es₁ → ∃ r ∈ log, r.id = f₁ i ∧ q r = true)
    (hmem₂ : ∀ i, i ∈ indicesP p es₂ → ∃ r ∈ log, r.id = f₂ i ∧ q r = true) :
    es₁.countP p + es₂.countP p ≤ log.countP q := by
  rw [← List.countP_append]
  refine countP_le_of_records (p := p) (es := es₁ ++ es₂)
    (fun i => if i < es₁.length then f₁ i else f₂ (i - es₁.length)) ?_ ?_
  · intro i j hi hj hf
    rw [mem_indicesP_append] at hi hj
    rcases hi with ⟨hi1, hi⟩ | ⟨hi1, hi⟩ <;> rcases hj with ⟨hj1, hj⟩ | ⟨hj1, hj⟩
    · simp only [hi1, hj1, ↓reduceIte] at hf
      exact hf₁ i j hi hj hf
    · have hj1' : ¬ j < es₁.length := by omega
      simp only [hi1, hj1', ↓reduceIte] at hf
      exact absurd hf (hdisj i _ hi hj)
    · have hi1' : ¬ i < es₁.length := by omega
      simp only [hi1', hj1, ↓reduceIte] at hf
      exact absurd hf.symm (hdisj j _ hj hi)
    · have hi1' : ¬ i < es₁.length := by omega
      have hj1' : ¬ j < es₁.length := by omega
      simp only [hi1', hj1', ↓reduceIte] at hf
      have := hf₂ _ _ hi hj hf
      omega
  · intro i hi
    rw [mem_indicesP_append] at hi
    rcases hi with ⟨hi1, hi⟩ | ⟨hi1, hi⟩
    · obtain ⟨r, hr, hid, hq⟩ := hmem₁ i hi
      refine ⟨r, hr, ?_, hq⟩
      simp only [hi1, ↓reduceIte]
      exact hid
    · obtain ⟨r, hr, hid, hq⟩ := hmem₂ _ hi
      have hn : ¬ i < es₁.length := by omega
      refine ⟨r, hr, ?_, hq⟩
      simp only [hn, ↓reduceIte]
      exact hid

end PTX.MBarrier
