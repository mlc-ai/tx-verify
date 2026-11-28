-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.PvFold

@[expose] public section

/-! # The maximum and the sum of a row's fold do not depend on the output dimension

The fold's maximum and sum read the scores only; the values (the second components of the pairs)
enter the numerator alone. The sum is nonnegative, and a positive sum has a finite maximum. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow
open SoftFold

theorem step_vals {α : Type} (sl : ℝ) (K : List α) (a b b' : α → ℝ) (st : St) :
    (step sl (K.map fun k => (a k, b k)) st).m = (step sl (K.map fun k => (a k, b' k)) st).m ∧
    (step sl (K.map fun k => (a k, b k)) st).l = (step sl (K.map fun k => (a k, b' k)) st).l := by
  have e : ∀ c : α → ℝ, blockMax (K.map fun k => (a k, c k)) =
      K.foldr (fun x y => max (a x : EReal) y) ⊥ := fun c => by
    unfold blockMax; rw [List.foldr_map]
  simp only [step]
  rw [e b, e b']
  simp [List.map_map, Function.comp_def]

theorem step_ml (sl : ℝ) (blk : List (ℝ × ℝ)) {st st' : St} (hm : st.m = st'.m)
    (hl : st.l = st'.l) : (step sl blk st).m = (step sl blk st').m ∧
      (step sl blk st).l = (step sl blk st').l := by
  obtain ⟨m, l, o⟩ := st
  obtain ⟨m', l', o'⟩ := st'
  dsimp only at hm hl
  subst hm hl
  exact ⟨rfl, rfl⟩

theorem kBlk_vals (P : Params) (r s tok h d i : Nat) :
    ∃ (K : List Nat) (a : Nat → ℝ) (b : Nat → ℝ),
      kBlk P r s tok h d i = K.map (fun k => (a k, b k)) ∧
      ∀ d', ∃ b' : Nat → ℝ, kBlk P r s tok h d' i = K.map (fun k => (a k, b' k)) :=
  ⟨_, fun k => (pair P r tok h d k).1 / P.scale, fun k => (pair P r tok h d k).2,
    by simp only [kBlk, blockList, List.map_map]; rfl,
    fun d' => ⟨fun k => (pair P r tok h d' k).2, by simp only [kBlk, blockList, List.map_map]; rfl⟩⟩

/-- **The maximum and the sum of the fold are the same for every output dimension.** -/
theorem kSt_ml_d (P : Params) (r s tok h d d' : Nat) (n : Nat) :
    (kSt P r s tok h d n).m = (kSt P r s tok h d' n).m ∧
      (kSt P r s tok h d n).l = (kSt P r s tok h d' n).l := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [kSt_succ, kSt_succ]
    obtain ⟨K, a, b, h1, h2⟩ := kBlk_vals P r s tok h d n
    obtain ⟨b', h3⟩ := h2 d'
    have e := step_vals (P.scale * log2eF32) K a b b' (kSt P r s tok h d n)
    rw [h1, h3]
    have f := step_ml (P.scale * log2eF32) (K.map fun k => (a k, b' k)) ih.1 ih.2
    exact ⟨e.1.trans f.1, e.2.trans f.2⟩

/-- **The sum of the fold is nonnegative, and a positive sum has a finite maximum.** -/
theorem kSt_l_pos (P : Params) (hs : 0 < P.scale * log2eF32) (r s tok h d n : Nat) :
    0 ≤ (kSt P r s tok h d n).l ∧
      (0 < (kSt P r s tok h d n).l → ∃ M : ℝ, (kSt P r s tok h d n).m = (M : EReal)) := by
  have I := run_inv (P.scale * log2eF32) hs ((List.range n).map (kBlk P r s tok h d))
  change Inv _ _ (kSt P r s tok h d n) at I
  by_cases hA : ((List.range n).map (kBlk P r s tok h d)).flatten = []
  · rw [I.1 hA]
    exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  · obtain ⟨M, hm, hl, -, -⟩ := I.2 hA
    refine ⟨?_, fun _ => ⟨M, hm⟩⟩
    rw [hl]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      positivity

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow
