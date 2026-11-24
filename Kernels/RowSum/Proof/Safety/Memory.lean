-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Values

@[expose] public section

/-! # `row_sum`: memory safety

Every access is to an allocated byte of `A` or `B`, no two accesses conflict, and no access is to
shared memory. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- **No two accesses conflict**: a row element is read once, an element of `B` is written once,
and `A` and `B` are disjoint. -/
theorem no_conflict (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) {e f : AsyncCopy.Ref} {a b : Acc} :
    ¬ Conflict X e f a b := by
  rintro ⟨hne, we, wf, hae, haf, hw, l, hl1, hl2⟩
  have hn := noTma_of_consistent noTma hX
  obtain ⟨e, rfl, hae⟩ := Execution.NoTma.intent_thread hn hae
  obtain ⟨f, rfl, haf⟩ := Execution.NoTma.intent_thread hn haf
  have acc : ∀ {v c w}, X.Access v c w →
      (w = false ∧ v.1 < M ∧ v.2 < K ∧ c = { loc := gA A K v.1 v.2, size := 4 }) ∨
      (w = true ∧ v.1 < M ∧ v.2 = K ∧ c = { loc := gB B v.1, size := 4 }) := by
    intro v c w h
    rcases h with ⟨bs, hr, rfl⟩ | ⟨bs, hw, rfl⟩ | ⟨old, new, hrmw⟩
    · obtain ⟨h1, h2, h3⟩ := reads_cases htf hX hr; exact .inl ⟨rfl, h1, h2, h3⟩
    · obtain ⟨-, h1, h2, h3⟩ := writes_cases htf hX hw; exact .inr ⟨rfl, h1, h2, h3⟩
    · exact absurd hrmw (no_rmw htf hX)
  rcases acc hae with ⟨rfl, h1, h1', rfl⟩ | ⟨rfl, h1, h1', rfl⟩ <;>
    rcases acc haf with ⟨rfl, h2, h2', rfl⟩ | ⟨rfl, h2, h2', rfl⟩
  · simp at hw
  · exact covers_gA_gB hpre h1 h1' h2 hl1 hl2
  · exact covers_gA_gB hpre h2 h2' h1 hl2 hl1
  · exact hne (congrArg AsyncCopy.Ref.thread (Prod.ext (covers_gB_gB hl1 hl2) (by omega)))

/-- **Every byte touched is allocated.** -/
theorem no_unalloc (hpre : Pre L A B M K x mem0) (htf : ThreadFacts L A B M K x X)
    (hX : Consistent L kernel Prod mem0 X) : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, ht, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · obtain ⟨e, heRef, htThread⟩ :=
      Execution.NoTma.memTouches_thread (noTma_of_consistent noTma hX) ht
    subst heRef
    rcases htThread with ⟨bs, hr⟩ | ⟨bs, hnc⟩ | ⟨bs, hw⟩ | ⟨old, new, hrmw⟩
    · obtain ⟨hgM, hjK, rfl⟩ := reads_cases htf hX hr
      have hrow := row_le hgM (show e.2 + 1 ≤ K by omega)
      simp only [Acc.Covers, Loc.InRange, gA] at hc
      obtain ⟨l1, l2, l3⟩ := l
      simp only at hc
      obtain ⟨rfl, rfl, h1, h2⟩ := hc
      have := hpre.input (K * e.1 + e.2) (by omega) (l3 - (A + 4 * (K * e.1 + e.2))) (by omega)
      rw [show A + 4 * (K * e.1 + e.2) + (l3 - (A + 4 * (K * e.1 + e.2))) = l3 by omega] at this
      rw [hn] at this
      simp at this
    · exact no_nc htf hX hnc
    · obtain ⟨-, hgM, -, rfl⟩ := writes_cases htf hX hw
      simp only [Acc.Covers, Loc.InRange, gB] at hc
      obtain ⟨l1, l2, l3⟩ := l
      simp only at hc
      obtain ⟨rfl, rfl, h1, h2⟩ := hc
      have := hpre.output (l3 - B) (by omega)
      rw [show B + (l3 - B) = l3 by omega] at this
      exact this hn
    · exact absurd hrmw (no_rmw htf hX)
  · exact absurd hu (noTma_of_consistent noTma hX).not_usesMbar

/-- **No access is to shared memory.** -/
theorem access_global (htf : ThreadFacts L A B M K x X) (hX : Consistent L kernel Prod mem0 X)
    {e : EvId} {a : Acc} {w : Bool} (h : X.Access e a w) : a.loc.space = .global := by
  rcases h with ⟨bs, hr, rfl⟩ | ⟨bs, hw, rfl⟩ | ⟨old, new, hrmw⟩
  · obtain ⟨-, -, rfl⟩ := reads_cases htf hX hr
    rfl
  · obtain ⟨-, -, -, rfl⟩ := writes_cases htf hX hw
    rfl
  · exact absurd hrmw (no_rmw htf hX)

end
end PTX.Kernels.RowSum.Proof
