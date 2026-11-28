-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.SoftFold
public import Kernels.InklingRelDecode.Proof.Lib.Geometry

@[expose] public section

/-!
# The row fold against the specification's sums

The blocks of a row are the blocks `s + i * splits` for `i < numIters`; block `i` holds the visible
keys in key order, each as the pair `(scale * S + bias, V[k, d])`. `SoftFold.run` of that list of
blocks is the kernel's `(m, l, o)` state, and its sums are the specification's `rowSum` and
`numerator` (`weight` is `SoftFold.W` of `log2eF32`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow

open Classical Finset

/-- The visible keys of iteration `i`. -/
noncomputable def blockKeys (P : Params) (r s tok i : Nat) : Finset Nat :=
  (keys P r s tok).filter fun k => k / 128 = s + i * P.splits

/-- The `(logit, value)` pair of a key for head `h`, dimension `d`. -/
noncomputable def pair (P : Params) (r tok h d k : Nat) : ℝ × ℝ :=
  (P.scale * score P r tok h k + bias P r tok h k, P.vVal r (h / group) k d)

/-- Block `i` of the row. -/
noncomputable def blockList (P : Params) (r s tok h d i : Nat) : List (ℝ × ℝ) :=
  ((blockKeys P r s tok i).sort (· ≤ ·)).map (pair P r tok h d)

/-- The blocks of the row. -/
noncomputable def rowBlocks (P : Params) (r s tok h d : Nat) : List (List (ℝ × ℝ)) :=
  (List.range (P.numIters r s)).map (blockList P r s tok h d)

/-- The kernel's final state of a row. -/
noncomputable def rowState (P : Params) (r s tok h d : Nat) : SoftFold.St :=
  SoftFold.run log2eF32 (rowBlocks P r s tok h d)

private theorem sum_blocks (P : Params) (r s tok h d : Nat) (F : ℝ × ℝ → ℝ) :
    ((rowBlocks P r s tok h d).flatten.map F).sum =
      ∑ i ∈ range (P.numIters r s), ∑ k ∈ blockKeys P r s tok i, F (pair P r tok h d k) := by
  have key : ∀ n : Nat, (((List.range n).map (blockList P r s tok h d)).flatten.map F).sum =
      ∑ i ∈ range n, ∑ k ∈ blockKeys P r s tok i, F (pair P r tok h d k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, List.map_append,
        List.sum_append, ih, sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, blockList, List.map_map]
      congr 1
      rw [← List.sum_toFinset _ (sort_nodup _ _), sort_toFinset]
      rfl
  exact key _

private theorem mem_keys {P : Params} {r s tok k : Nat} :
    k ∈ keys P r s tok ↔ k < P.blocks r * 128 ∧ P.inSplit r s k ∧ k ≤ P.past r + tok := by
  simp [keys]

private theorem blockKeys_eq (P : Params) (hsp : 0 < P.splits) (r s tok i : Nat) :
    blockKeys P r s tok i =
      (keys P r s tok).filter fun k => (k / 128 - s) / P.splits = i := by
  ext k
  rw [blockKeys, mem_filter, mem_filter]
  refine and_congr_right fun hk => ?_
  obtain ⟨-, ⟨h1, h2, -⟩, -⟩ := mem_keys.1 hk
  constructor
  · intro h5
    rw [h5]
    simp [Nat.mul_div_cancel _ hsp]
  · intro h5
    have := Nat.div_add_mod (k / 128 - s) P.splits
    rw [h2, h5, Nat.mul_comm] at this
    omega

private theorem sum_keys (P : Params) (hsp : 0 < P.splits) (r s tok h d : Nat)
    (F : ℝ × ℝ → ℝ) :
    ((rowBlocks P r s tok h d).flatten.map F).sum =
      ∑ k ∈ keys P r s tok, F (pair P r tok h d k) := by
  rw [sum_blocks]
  simp only [blockKeys_eq P hsp]
  refine sum_fiberwise_of_maps_to (g := fun k => (k / 128 - s) / P.splits) ?_
    (fun k => F (pair P r tok h d k))
  intro k hk
  obtain ⟨-, hs, -⟩ := mem_keys.1 hk
  obtain ⟨-, i, hi, hk3⟩ := (numIters_spec (r := r) (s := s) (k := k) hsp).1 hs
  rw [mem_range]
  have : (k / 128 - s) / P.splits = i := by rw [hk3]; simp [Nat.mul_div_cancel _ hsp]
  rw [this]
  exact hi

theorem log2e_pos : 0 < log2eF32 := by norm_num [log2eF32]

private theorem flat_sum (P : Params) (hsp : 0 < P.splits) (r s tok h d : Nat) :
    ((rowBlocks P r s tok h d).flatten.map fun q => SoftFold.W log2eF32 q.1).sum =
        rowSum P r s tok h ∧
      ((rowBlocks P r s tok h d).flatten.map fun q => SoftFold.W log2eF32 q.1 * q.2).sum =
        numerator P r s tok h d :=
  ⟨sum_keys P hsp r s tok h d _, sum_keys P hsp r s tok h d _⟩

/-- A row with no visible key has the empty state, any other row has a positive denominator. -/
theorem rowSum_zero_iff (P : Params) (hsp : 0 < P.splits) (r s tok h d : Nat) :
    rowSum P r s tok h = 0 ↔ (rowState P r s tok h d).l = 0 := by
  obtain ⟨hS, -⟩ := flat_sum P hsp r s tok h d
  by_cases e : (rowBlocks P r s tok h d).flatten = []
  · rw [e] at hS
    simp only [List.map_nil, List.sum_nil] at hS
    exact iff_of_true hS.symm (SoftFold.fold_empty _ log2e_pos _ e).1
  · obtain ⟨-, hl⟩ := SoftFold.fold_normalized _ log2e_pos _ e
    rw [← hS]
    exact iff_of_false (SoftFold.sumW_pos _ e).ne' hl.ne'

/-- **The normalized output of the row fold is `oPart`.** -/
theorem oPart_eq (P : Params) (hsp : 0 < P.splits) (r s tok h d : Nat) :
    oPart P r s tok h d = (rowState P r s tok h d).o / (rowState P r s tok h d).l := by
  obtain ⟨hS, hN⟩ := flat_sum P hsp r s tok h d
  by_cases e : (rowBlocks P r s tok h d).flatten = []
  · obtain ⟨hl, ho, -⟩ := SoftFold.fold_empty _ log2e_pos _ e
    have : rowSum P r s tok h = 0 := (rowSum_zero_iff P hsp r s tok h d).2 hl
    have ho' : (rowState P r s tok h d).o = 0 := ho
    simp [oPart, this, ho']
  · obtain ⟨hq, -⟩ := SoftFold.fold_normalized _ log2e_pos _ e
    have : rowSum P r s tok h ≠ 0 := by
      rw [← hS]
      exact (SoftFold.sumW_pos _ e).ne'
    simp only [oPart, this, ↓reduceIte]
    rw [← hS, ← hN]
    exact hq.symm

/-- **The log2 normalizer of a nonempty row is the fold's `m * sl + log2 l`.** -/
theorem lsePart_eq (P : Params) (hsp : 0 < P.splits) (r s tok h d : Nat)
    (nz : rowSum P r s tok h ≠ 0) :
    lsePart P r s tok h = (rowState P r s tok h d).m.toReal * log2eF32 +
      Real.logb 2 (rowState P r s tok h d).l := by
  obtain ⟨hS, -⟩ := flat_sum P hsp r s tok h d
  have e : (rowBlocks P r s tok h d).flatten ≠ [] := by
    intro e
    rw [e] at hS
    exact nz (by simpa using hS.symm)
  rw [lsePart, ← hS]
  exact (SoftFold.fold_lse _ log2e_pos _ e).symm

end PTX.Kernels.InklingRelDecode.Proof.Lib.SoftRow
