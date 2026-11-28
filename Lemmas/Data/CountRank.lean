-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # Every rank below the count of marked entries is the rank of a marked entry

A proof tool, kernel independent: in the first `n` entries of a list with `c` entries marked by
`p`, the marked entry with `r` marked entries before it exists for every `r < c`. -/

namespace PTX

theorem exists_rank {α : Type} (p : α → Bool) (l : List α) :
    ∀ n r, r < (l.take n).countP p → ∃ k < n, ∃ e, l[k]? = some e ∧ p e = true ∧
      (l.take k).countP p = r := by
  intro n
  induction n with
  | zero => intro r h; simp at h
  | succ n ih =>
    intro r h
    by_cases hr : r < (l.take n).countP p
    · obtain ⟨k, hk, e, he, hp, hc⟩ := ih r hr
      exact ⟨k, by omega, e, he, hp, hc⟩
    · cases hn : l[n]? with
      | none => simp [List.take_add_one, hn] at h; omega
      | some e =>
        simp only [List.take_add_one, hn, Option.toList_some, List.countP_append,
          List.countP_cons, List.countP_nil] at h
        cases hpe : p e
        · simp [hpe] at h; omega
        · refine ⟨n, by omega, e, hn, hpe, ?_⟩
          simp [hpe] at h; omega

end PTX
