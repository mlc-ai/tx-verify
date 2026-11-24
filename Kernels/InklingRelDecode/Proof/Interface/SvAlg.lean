-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.Softmax

@[expose] public section

/-!
# The softmax step depends on a block through the multiset of its scores

The two lanes of a tile row hold the row's 128 columns in two halves; the thread of the first half
sees the row's block as `own ++ peer`, the thread of the second as `peer ++ own`, while
`Softmax.run` is stated over the block in key order. The running maximum and sum after a step
depend on the block through the maximum of its scores and the sum of the weights of its scores
only, so a permutation of the score list leaves them unchanged (`step_ml_perm`).

`run_m_ne_top`: the running maximum is never `+inf` (the machine reads it back with `eOf`).
-/

namespace PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical

theorem blockMax_ne_top : ∀ blk : List (ℝ × ℝ), blockMax blk ≠ ⊤
  | [] => by simp [blockMax_nil]
  | q :: t => by
    have h : blockMax (q :: t) = max (q.1 : EReal) (blockMax t) := rfl
    rw [h]
    intro hm
    have := max_eq_top.mp hm
    rcases this with h1 | h2
    · exact EReal.coe_ne_top _ h1
    · exact blockMax_ne_top t h2

theorem step_m_ne_top (sl : ℝ) (blk : List (ℝ × ℝ)) {st : St} (h : st.m ≠ ⊤) :
    (step sl blk st).m ≠ ⊤ := by
  unfold step
  simp only
  split_ifs
  · exact h
  · intro hm
    rcases max_eq_top.mp hm with h1 | h2
    · exact h h1
    · exact blockMax_ne_top blk h2

theorem run_m_ne_top (sl : ℝ) (bs : List (List (ℝ × ℝ))) : (run sl bs).m ≠ ⊤ := by
  unfold run
  suffices ∀ st : St, st.m ≠ ⊤ → (bs.foldl (fun st blk => step sl blk st) st).m ≠ ⊤ from
    this _ (by simp)
  induction bs with
  | nil => intro st h; exact h
  | cons b t ih =>
    intro st h
    exact ih _ (step_m_ne_top sl b h)

theorem blockMax_eq_foldr (blk : List (ℝ × ℝ)) :
    blockMax blk =
      (blk.map Prod.fst).foldr (fun (x : ℝ) (acc : EReal) => max (x : EReal) acc) ⊥ := by
  unfold blockMax
  induction blk with
  | nil => rfl
  | cons a t ih => simp only [List.foldr, List.map_cons, ih]

theorem blockMax_perm {blk blk' : List (ℝ × ℝ)}
    (h : (blk.map Prod.fst).Perm (blk'.map Prod.fst)) : blockMax blk = blockMax blk' := by
  rw [blockMax_eq_foldr, blockMax_eq_foldr]
  have : LeftCommutative (fun (x : ℝ) (acc : EReal) => max (x : EReal) acc) :=
    ⟨fun a b c => max_left_comm _ _ _⟩
  exact h.foldr_eq _

theorem sum_perm {blk blk' : List (ℝ × ℝ)} (f : ℝ → ℝ)
    (h : (blk.map Prod.fst).Perm (blk'.map Prod.fst)) :
    (blk.map fun q => f q.1).sum = (blk'.map fun q => f q.1).sum := by
  have := (h.map f).sum_eq
  simpa [List.map_map, Function.comp_def] using this

end
end PTX.Kernels.InklingRelDecode.Softmax
