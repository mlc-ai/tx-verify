-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0TcRank

@[expose] public section

/-! # The interval of each block of Tensor Memory collectives -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcPositions

open PTX TcCollectiveSites Wg0TcRank

/-- The number of data collectives in the completed sparse blocks. -/
def beforeBlock (vote : Nat → Bool) (i : Nat) : Nat := 3 * i + 16 * priorRescales vote i

theorem beforeBlock_succ (vote : Nat → Bool) (i : Nat) :
    beforeBlock vote (i + 1) =
      beforeBlock vote i + 3 + 16 * ((i != 0) && vote i).toNat := by
  simp only [beforeBlock, priorRescales]
  omega

theorem beforeBlock_mono (vote : Nat → Bool) : Monotone (beforeBlock vote) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [beforeBlock_succ]
  omega

/-- The output loads and waits form a final eight-event interval following the sparse loop. -/
def blockIndex (d : Wg0.D) : Nat := if d.site.inEpilogue then d.block + 1 else d.block

/-- Each data event has a rank in its sparse block or in the output epilogue. -/
theorem interval {vote : Nat → Bool} {d : Wg0.D} (hs : Scheduled vote d) (hd : DataSite d.site)
    (ha : d.site.inRescale = true → d.rescale = true) :
    beforeBlock vote (blockIndex d) ≤ rank vote d ∧
      rank vote d < if d.site.inEpilogue then beforeBlock vote (blockIndex d) + 8
      else beforeBlock vote (blockIndex d + 1) := by
  generalize hsite : d.site = s at hd
  cases hd <;> simp only [blockIndex, rank, hsite, Wg0.Site.inEpilogue, Bool.false_eq_true,
    ite_false, ite_true, blockOffset]
  all_goals simp only [beforeBlock, priorRescales]
  all_goals try (solve | constructor <;> omega)
  all_goals first
    | (have hSite : d.site.inRescale = true := by rw [hsite]; rfl
       have hFlag := (hs.2 (.inl hSite)).symm.trans (ha hSite)
       simp only [hFlag, Bool.toNat_true]
       constructor <;> omega)
    | (have hc := hs.2 (.inr (by rw [hsite]; rfl))
       rw [hc]
       constructor <;> omega)

private theorem block_bound {d : Wg0.D} {n : Nat} (hn : d.block < n) : blockIndex d ≤ n := by
  unfold blockIndex
  split <;> omega

/-- Every score, rescale or output collective lies before the final closing sequence. -/
theorem before_final {vote : Nat → Bool} {d : Wg0.D} {n : Nat}
    (hs : Scheduled vote d) (hd : DataSite d.site)
    (ha : d.site.inRescale = true → d.rescale = true)
    (hn : d.block < n) : rank vote d < beforeBlock vote n + 8 := by
  have hi := (interval hs hd ha).2
  unfold blockIndex at hi
  split at hi
  · have hl := beforeBlock_mono vote (show d.block + 1 ≤ n by omega)
    omega
  · have hl := beforeBlock_mono vote (show d.block + 1 ≤ n by omega)
    omega

/-- Both final sites follow all sparse-block collectives and all eight output collectives. -/
theorem finished_data {vote : Nat → Bool} {d : Wg0.D} {n : Nat}
    (hs : Scheduled vote d) (hd : d.site = .commit ∨ d.site = .exit)
    (hn : d.block + 1 = n) : rank vote d = beforeBlock vote n + 8 := by
  have hRescale : d.rescale = ((d.block != 0) && vote d.block) :=
    hs.2 (.inr (by rcases hd with hh | hh <;> rw [hh] <;> rfl))
  rw [← hn, beforeBlock_succ]
  rcases hd with hh | hh <;> simp only [rank, hh, blockOffset, beforeBlock, hRescale]
  all_goals omega

/-- The ordinal identifies whether a collective belongs to a sparse block or to the output. -/
theorem same_block {vote : Nat → Bool} {d f : Wg0.D} {n : Nat}
    (hs : Scheduled vote d) (hs' : Scheduled vote f)
    (hd : DataSite d.site) (hf : DataSite f.site)
    (ha : d.site.inRescale = true → d.rescale = true)
    (ha' : f.site.inRescale = true → f.rescale = true)
    (hn : d.block < n) (hn' : f.block < n)
    (he : d.site.inEpilogue = true → d.block + 1 = n)
    (he' : f.site.inEpilogue = true → f.block + 1 = n)
    (hr : rank vote d = rank vote f) :
    d.block = f.block ∧ d.site.inEpilogue = f.site.inEpilogue := by
  obtain ⟨hdlo, hdhi⟩ := interval hs hd ha
  obtain ⟨hflo, hfhi⟩ := interval hs' hf ha'
  have hblock : blockIndex d = blockIndex f := by
    apply Nat.le_antisymm
    · by_contra! hlt
      have hnot : f.site.inEpilogue = false := by
        cases h : f.site.inEpilogue
        · rfl
        · have hb := block_bound hn
          have hfEnd : blockIndex f = n := by simp only [blockIndex, h, ↓reduceIte, he' h]
          rw [hfEnd] at hlt
          omega
      simp only [hnot, Bool.false_eq_true, ↓reduceIte] at hfhi
      have hm := beforeBlock_mono vote (show blockIndex f + 1 ≤ blockIndex d by omega)
      omega
    · by_contra! hlt
      have hnot : d.site.inEpilogue = false := by
        cases h : d.site.inEpilogue
        · rfl
        · have hb := block_bound hn'
          have hdEnd : blockIndex d = n := by simp only [blockIndex, h, ↓reduceIte, he h]
          rw [hdEnd] at hlt
          omega
      simp only [hnot, Bool.false_eq_true, ↓reduceIte] at hdhi
      have hm := beforeBlock_mono vote (show blockIndex d + 1 ≤ blockIndex f by omega)
      omega
  cases h : d.site.inEpilogue <;> cases h' : f.site.inEpilogue
  all_goals simp only [blockIndex, h, h', Bool.false_eq_true, ↓reduceIte] at hblock
  all_goals try (have := he h; omega)
  all_goals try (have := he' h'; omega)
  all_goals exact ⟨by omega, rfl⟩

private theorem data_rank {vote : Nat → Bool} {d : Wg0.D} (h : DataSite d.site) :
    rank vote d = beforeBlock vote d.block + blockOffset d.rescale d.site := by
  generalize hSite : d.site = s at h
  cases h <;> simp only [rank, hSite, beforeBlock]

private theorem score_arm {P : Params} {L : Launch} {g : Nat} {d : Wg0.D}
    (h : Wg0.Inv P L g d) {a k : Fin 2} (hsite : d.site = .scoreLoad a k) :
    a.val = Wg0.arm L g := by
  obtain ⟨j, hj⟩ := h.armSite ⟨a, k, hsite⟩
  exact congrArg Fin.val (Wg0.Site.scoreLoad.inj (hsite.symm.trans hj)).1

/-- Equal ordinals in one warp identify the same Tensor Memory data site. -/
theorem same_site {P : Params} {L : Launch} {g h : Nat} {d f : Wg0.D} {vote : Nat → Bool}
    (hi : Wg0.Inv P L g d) (hi' : Wg0.Inv P L h f)
    (hs : Scheduled vote d) (hs' : Scheduled vote f)
    (hd : DataSite d.site) (hf : DataSite f.site)
    (hBlocks : Wg0.blocksOf P L g = Wg0.blocksOf P L h)
    (hArm : Wg0.arm L g = Wg0.arm L h)
    (hr : rank vote d = rank vote f) : d.site = f.site := by
  have hb' := hi'.blockLt
  rw [← hBlocks] at hb'
  have he' (hf : f.site.inEpilogue = true) : f.block + 1 = Wg0.blocksOf P L g :=
    (hi'.epilogueLast hf).trans hBlocks.symm
  obtain ⟨hb, hEpi⟩ := same_block hs hs' hd hf hi.rescaleArm hi'.rescaleArm
    hi.blockLt hb' hi.epilogueLast he' hr
  have hRescale (hde : pastRescale d.site = true) (hfe : pastRescale f.site = true) :
      d.rescale = f.rescale := by
    rw [hs.2 (.inr hde), hs'.2 (.inr hfe), hb]
  rw [data_rank hd, data_rank hf, hb] at hr
  have ho := Nat.add_left_cancel hr
  generalize hSite : d.site = s at hd ⊢
  generalize hSite' : f.site = t at hf ⊢
  cases hd <;> cases hf
  all_goals simp only [hSite, hSite', Wg0.Site.inEpilogue, Bool.false_eq_true] at hEpi
  all_goals try contradiction
  all_goals simp only [hSite, hSite', blockOffset] at ho
  all_goals try (rw [hRescale (by rw [hSite]; rfl) (by rw [hSite']; rfl)] at ho)
  all_goals try omega
  case scoreLoad.scoreLoad a k a' k' =>
    have ha : a = a' := Fin.ext ((score_arm hi hSite).trans
      (hArm.trans (score_arm hi' hSite').symm))
    have hk : k = k' := Fin.ext ho
    rw [ha, hk]
  all_goals congr 1
  all_goals apply Fin.ext
  all_goals omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0TcPositions
