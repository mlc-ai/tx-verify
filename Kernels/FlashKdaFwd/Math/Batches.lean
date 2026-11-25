-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Math.Sequence

@[expose] public section
namespace PTX.Kernels.FlashKdaFwd.Math.Batches
open Finset Recurrence

@[simp] theorem firstTile_succ (length : ℕ → ℕ) (i : ℕ) :
    firstTile length (i+1) = firstTile length i + tiles (length i) := by
  simp [firstTile, sum_range_succ]

@[simp] theorem firstToken_succ (length : ℕ → ℕ) (i : ℕ) :
    firstToken length (i+1) = firstToken length i + length i := by
  simp [firstToken, sum_range_succ]

theorem monotone_token (length : ℕ → ℕ) : Monotone (firstToken length) :=
  monotone_nat_of_le_succ fun i => by rw [firstToken_succ]; omega

theorem token_lt_end (length : ℕ → ℕ) {seq count t : ℕ} (hs : seq < count) (ht : t < length seq) :
    firstToken length seq + t < firstToken length count := by
  have h := monotone_token length (show seq+1 ≤ count from hs)
  rw [firstToken_succ] at h
  omega

theorem token_unique (length : ℕ → ℕ) {i j ti tj : ℕ} (hi : ti < length i) (hj : tj < length j)
    (same : firstToken length i + ti = firstToken length j + tj) : i = j ∧ ti = tj := by
  rcases lt_trichotomy i j with h | h | h
  · have := token_lt_end length h hi
    omega
  · exact ⟨h, by simpa [h] using same⟩
  · have := token_lt_end length h hj
    omega

/-- The packed batch has no gaps: every global token index below the total belongs to exactly
one sequence (`token_unique`), as one of its tokens. -/
theorem token_owner (length : ℕ → ℕ) {count token : ℕ} (h : token < firstToken length count) :
    ∃ seq < count, ∃ t < length seq, token = firstToken length seq + t := by
  induction count with
  | zero => simp [firstToken] at h
  | succ n ih =>
    rw [firstToken_succ] at h
    by_cases hn : token < firstToken length n
    · obtain ⟨seq, hs, t, ht, e⟩ := ih hn
      exact ⟨seq, by omega, t, ht, e⟩
    · exact ⟨n, by omega, token - firstToken length n, by omega, by omega⟩

theorem monotone_tile (length : ℕ → ℕ) : Monotone (firstTile length) :=
  monotone_nat_of_le_succ fun i => by rw [firstTile_succ]; omega

theorem allocation (length : ℕ → ℕ) (count : ℕ) :
    firstTile length count ≤ tiles (firstToken length count) + count := by
  induction count with
  | zero => simp [firstTile, firstToken, tiles]
  | succ n ih =>
    rw [firstTile_succ]
    have h : firstToken length (n+1) = firstToken length n + length n := by
      simp [firstToken, sum_range_succ]
    rw [h]
    unfold tiles at *
    omega

theorem unique_owner (length : ℕ → ℕ) {i j tile : ℕ}
    (hi : firstTile length i ≤ tile) (ei : tile < firstTile length (i+1))
    (hj : firstTile length j ≤ tile) (ej : tile < firstTile length (j+1)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim ((not_lt_of_ge (monotone_tile length (Nat.succ_le_of_lt h)))
      (lt_of_le_of_lt hj ei))
  · exact h
  · exact False.elim ((not_lt_of_ge (monotone_tile length (Nat.succ_le_of_lt h)))
      (lt_of_le_of_lt hi ej))

def search (starts : ℕ → ℕ) (tile lo hi : ℕ) : ℕ :=
  if h : lo+1 < hi then
    let mid := (lo+hi)/2
    if starts mid ≤ tile then search starts tile mid hi else search starts tile lo mid
  else lo
termination_by hi-lo
decreasing_by all_goals omega

theorem search_owner (starts : ℕ → ℕ) (tile lo hi : ℕ)
    (hlo : starts lo ≤ tile) (hhi : tile < starts hi) (h : lo < hi) :
    let i := search starts tile lo hi
    lo ≤ i ∧ i < hi ∧ starts i ≤ tile ∧ tile < starts (i+1) := by
  rw [search]
  split
  · rename_i more
    dsimp only
    split
    · rename_i hm
      have bounds :=  search_owner starts tile ((lo+hi)/2) hi hm hhi (by omega)
      try dsimp only at bounds ⊢
      exact ⟨by omega, bounds.2⟩
    · rename_i hm
      have bounds :=  search_owner starts tile lo ((lo+hi)/2) hlo (by omega) (by omega)
      try dsimp only at bounds ⊢
      exact ⟨bounds.1, by omega, bounds.2.2⟩
  · rename_i small
    have : lo+1 = hi := by omega
    simp [h, hlo, this, hhi]
termination_by hi-lo
decreasing_by all_goals omega

theorem search_surplus (starts : ℕ → ℕ) (mono : Monotone starts) (tile lo hi : ℕ)
    (h : lo < hi) (excess : starts hi ≤ tile) : search starts tile lo hi + 1 = hi := by
  rw [search]
  split
  · have hm : starts ((lo+hi)/2) ≤ tile := le_trans (mono (by omega)) excess
    simp only [hm, ite_true]
    exact search_surplus starts mono tile ((lo+hi)/2) hi (by omega) excess
  · omega
termination_by hi-lo
decreasing_by omega

theorem workspace_index {stride h₁ h₂ t₁ t₂ : ℕ} (ht₁ : t₁ < stride) (ht₂ : t₂ < stride)
    (heq : h₁*stride+t₁ = h₂*stride+t₂) : h₁ = h₂ ∧ t₁ = t₂ := by
  have pos := Nat.zero_lt_of_lt ht₁
  have hh := congrArg (fun k => k / stride) heq
  simp [Nat.mul_comm h₁ stride, Nat.mul_comm h₂ stride, Nat.mul_add_div pos,
    Nat.div_eq_of_lt ht₁, Nat.div_eq_of_lt ht₂] at hh
  exact ⟨hh, by simpa [hh] using heq⟩

end PTX.Kernels.FlashKdaFwd.Math.Batches
