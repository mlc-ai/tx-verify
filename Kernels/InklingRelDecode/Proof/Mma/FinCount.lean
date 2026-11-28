-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.MmaHistory
public import Kernels.InklingRelDecode.Proof.Mma.CoverHist

@[expose] public section

/-! # The counter at the final sites

The loop's counter is the number of blocks plus one at the final sites: they are reached from the
iteration step of the last block (`iterNext`), or at zero from the start. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Frame

/-- The counter at a final site. -/
def FinCount (d : D) : Prop := finS d.site = true → d.i = d.limit + 1 ∨ d.i = 0

private theorem issue_qk (j : Fin 8) : finS (issueNext Site.qk Site.qkCommit j) = false := by
  unfold issueNext; split_ifs <;> rfl

private theorem issue_pv (j : Fin 8) : finS (issueNext Site.pv Site.pvCommit1 j) = false := by
  unfold issueNext; split_ifs <;> rfl

local macro "fin_goal" : tactic =>
  `(tactic| first | (simp [finS]; done) | (intro h; simp [issue_qk, issue_pv] at h))

/-- The steps of the machine: the next state keeps the counter, or is one of the loop's two
advances, or reads the loop bound at the start. -/
private theorem next_shape {L g d d' e} (move : next L g d e = some (some d')) :
    (∃ s, d' = { d with site := s } ∧ (finS s = true → finS d.site = true ∨ d.site = .bar0)) ∨
      d' = iterNext d ∨ d' = afterQk d ∨
      ∃ v, d' = { d with site := .bar0, word := v } := by
  obtain ⟨s, i, v⟩ := d
  cases s <;> simp only [next] at move <;>
    try (obtain rfl := Option.some.inj (Option.some.inj move);
         first | exact Or.inl ⟨_, rfl, by fin_goal⟩ | simp)
  all_goals
    obtain ⟨pc, k⟩ := e
    cases k <;> (try simp only at move) <;> (try split at move) <;>
      try first
        | (obtain rfl := Option.some.inj (Option.some.inj move);
           first | exact Or.inl ⟨_, rfl, by fin_goal⟩ | simp)
        | (simp at move; done)
  all_goals
    rename_i bs
    cases hh : Except.toOption (rebuild 3 bs) <;> simp [hh] at move
    obtain rfl := move
    simp

private theorem finCount_next {L g d d' e} (inv : Inv d) (ih : FinCount d)
    (move : next L g d e = some (some d')) : FinCount d' := by
  have iter (x : D) : FinCount (iterNext x) := by
    unfold FinCount iterNext D.limit
    by_cases h : x.i = low x.word
    · simp [h, finS]
    · intro hf
      by_cases h2 : x.i + 1 < low x.word <;> simp [h, h2, finS] at hf
  rcases next_shape move with ⟨s, rfl, hfin⟩ | rfl | rfl | ⟨w, rfl⟩
  · intro hs
    rcases hfin hs with h | h
    · exact ih h
    · have h0 : d.i = 0 := by simpa only [Inv, h] using inv
      simp [h0]
  · exact iter d
  · unfold afterQk
    split_ifs
    · exact iter d
    · intro h
      simp [finS] at h
  · intro h
    simp [finS] at h

/-- **The counter of the lane at a final site**, from the history of its steps. -/
theorem mma_fin_count {Q L m X g k w x round d n} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (words : RoleBytes L X)
    (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some (workerState w x (.mma round) d n)))
    (zero : n .ub = 0) : FinCount d :=
  mma_history_at hp hX hf words (fun d _ => FinCount d) (fun _ _ => by simp [FinCount, finS])
    (fun _ _ _ _ _ _ _ _ _ inv _ _ _ ih move => finCount_next inv ih move) hk hs zero

end PTX.Kernels.InklingRelDecode.Proof.Mma
