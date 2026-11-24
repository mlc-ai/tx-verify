-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.List.Nodup

@[expose] public section

/-! # Distinct images of selected elements

A proof tool. When the images of the selected elements of a list are distinct, two selected
positions with one image are one position (`nodup_filter_map_idx`): a thread's run invariant
that its initializations are distinct says that an initialization is its thread's only one. -/

namespace PTX.Flow

theorem nodup_filter_map_idx {α β : Type} {p : α → Bool} {f : α → β} :
    ∀ {l : List α}, ((l.filter p).map f).Nodup → ∀ {i j : Nat} (hi : i < l.length)
      (hj : j < l.length), p l[i] = true → p l[j] = true → f l[i] = f l[j] → i = j
  | [], _, _, _, hi, _, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, hnd, i, j, hi, hj, hpi, hpj, hf => by
    have htail : ((l.filter p).map f).Nodup := by
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, List.map_cons] at hnd
        exact (List.nodup_cons.mp hnd).2
      · rw [List.filter_cons_of_neg ha] at hnd
        exact hnd
    have hmem : ∀ k (hk : k < l.length), p l[k] = true → p a = true → f l[k] ≠ f a := by
      intro k hk hpk ha he
      rw [List.filter_cons_of_pos ha, List.map_cons] at hnd
      refine (List.nodup_cons.mp hnd).1 ?_
      rw [← he]
      exact List.mem_map_of_mem (List.mem_filter.mpr ⟨List.getElem_mem hk, hpk⟩)
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj hf
        exact absurd hf.symm (hmem j (by simp at hj; omega) hpj hpi)
    | succ i =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hpi hpj hf
        exact absurd hf (hmem i (by simp at hi; omega) hpi hpj)
      | succ j =>
        simp only [List.getElem_cons_succ] at hpi hpj hf
        exact congrArg (· + 1)
          (nodup_filter_map_idx htail (by simp at hi; omega) (by simp at hj; omega) hpi hpj hf)

end PTX.Flow
