-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Lib.PvFold
public import Kernels.InklingRelDecode.Proof.Lib.SoftLane
import Kernels.InklingRelDecode.Proof.Lib.Rows

@[expose] public section

/-! # The maximum of a block is the maximum of its two halves

The kernel's score of a key is `bias / scale + score` when the key is visible. The maximum of a
block of the fold (`blockMax`) is the maximum of these over the 128 columns of the block, which is
the larger of the maxima of the two halves of 64 columns the two lanes of a row work on. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX Finset SoftRow Classical

/-- **The kernel's score of a key**: `-inf` if the token does not see it. -/
noncomputable def keyX (P : Params) (r tok h k : Nat) : EReal :=
  if k ≤ P.past r + tok then
    ((bias P r tok h k * (1 / P.scale) + score P r tok h k : ℝ) : EReal) else ⊥

/-- The score of column `c` of the block `s + i * splits`. -/
noncomputable def colX (P : Params) (r s tok h i c : Nat) : EReal :=
  keyX P r tok h (128 * (P.splits * i + s) + c)

theorem sup_ite_bot (p : Nat → Prop) [DecidablePred p] (f : Nat → EReal) (s : Finset Nat) :
    s.sup (fun c => if p c then f c else ⊥) = (s.filter p).sup f := by
  rw [Finset.sup_ite]; simp

theorem foldr_sup (l : List Nat) (f : Nat → EReal) :
    l.foldr (fun k acc => max (f k) acc) ⊥ = l.toFinset.sup f := by
  induction l with
  | nil => simp
  | cons k l ih => simp [ih]

/-- **The block's maximum is the maximum of the scores of its visible columns.** -/
theorem blockMax_eq {P : Params} {r s tok h d i : Nat} (hs : 0 < P.splits) (hsc : 0 < P.scale)
    (hi : i < P.numIters r s) :
    SoftFold.blockMax (kBlk P r s tok h d i) = (range 128).sup (colX P r s tok h i) := by
  have key : blockKeys P r s tok i =
      ((range 128).filter fun c => 128 * (P.splits * i + s) + c ≤ P.past r + tok).image
        (fun c => 128 * (P.splits * i + s) + c) := by
    have hb := blk_lt hs hi
    ext k
    unfold blockKeys keys
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    simp only [Params.inSplit, mem_filter, mem_range]
    have hm : P.splits * i = i * P.splits := Nat.mul_comm _ _
    constructor
    · rintro ⟨⟨-, -, hk⟩, hd⟩
      exact ⟨k - 128 * (P.splits * i + s), ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨c, ⟨hc, hv⟩, rfl⟩
      have hq : (128 * (P.splits * i + s) + c) / 128 = P.splits * i + s := by omega
      refine ⟨⟨by omega, ⟨by omega, ?_, by omega⟩, hv⟩, by omega⟩
      rw [hq, Nat.add_sub_cancel]
      exact Nat.mul_mod_right _ _
  have e : SoftFold.blockMax (kBlk P r s tok h d i) =
      (blockKeys P r s tok i).sup fun k => (((pair P r tok h d k).1 / P.scale : ℝ) : EReal) := by
    unfold SoftFold.blockMax kBlk blockList
    rw [List.map_map, List.foldr_map]
    have := foldr_sup ((blockKeys P r s tok i).sort (· ≤ ·))
      fun k => (((pair P r tok h d k).1 / P.scale : ℝ) : EReal)
    rw [Finset.sort_toFinset] at this
    exact this
  rw [e, key, Finset.sup_image, ← sup_ite_bot]
  refine Finset.sup_congr rfl fun c _ => ?_
  unfold colX keyX pair
  dsimp only
  have hne := hsc.ne'
  have hb : ∀ a b : ℝ, (P.scale * a + b) / P.scale = b * (1 / P.scale) + a := fun a b => by
    field_simp
    ring
  split_ifs
  · simp only [Function.comp_apply, hb]
  · rfl

/-- The maximum of the scores of the 64 columns of half `hf` of a block. -/
noncomputable def halfMax (P : Params) (r s tok h i hf : Nat) : EReal :=
  (range 64).sup fun c => colX P r s tok h i (64 * hf + c)

theorem sup128 (F : Nat → EReal) :
    (range 128).sup F = max ((range 64).sup F) ((range 64).sup fun c => F (64 + c)) := by
  apply le_antisymm
  · refine Finset.sup_le fun c hc => ?_
    by_cases h : c < 64
    · exact le_max_of_le_left (Finset.le_sup (f := F) (mem_range.2 h))
    · have h2 : c - 64 < 64 := by have := mem_range.1 hc; omega
      have h3 := Finset.le_sup (f := fun c => F (64 + c)) (mem_range.2 h2)
      rw [show 64 + (c - 64) = c by omega] at h3
      exact le_max_of_le_right h3
  · refine max_le (Finset.sup_le fun c hc => Finset.le_sup (mem_range.2 (by
      have := mem_range.1 hc; omega))) (Finset.sup_le fun c hc => Finset.le_sup (mem_range.2 (by
      have := mem_range.1 hc; omega)))

/-- **The block's maximum is the larger of its two halves'.** -/
theorem blockMax_halves {P : Params} {r s tok h d i : Nat} (hs : 0 < P.splits)
    (hsc : 0 < P.scale) (hi : i < P.numIters r s) :
    SoftFold.blockMax (kBlk P r s tok h d i) =
      max (halfMax P r s tok h i 0) (halfMax P r s tok h i 1) := by
  rw [blockMax_eq hs hsc hi, sup128]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Lib
