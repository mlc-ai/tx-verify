-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ref

@[expose] public section

/-! # The index warp's loop counters along the transitions

Each transition of the control machine (`Machine.lean`, `Lib/IndexVal.lean`) leads to a site
whose counters (`Ctr`, `Ref.lean`) hold in the block the reference invariant assigns: the set-up
(`ctr_first`, `ctr_afterA`, `ctr_lens`, `ctr_afterPre`) in block 0, a main block's end
(`ctr_mainEnd`) and an extra block's end (`ctr_xEnd`) in the next block, the extra cache's first
pair (`ctr_afterXpre`) in block `M`. A skipped main loop has no block at all (`ctr_noMain`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The main loop's head in block `i`. -/
theorem ctr_mainTop {c : IxCtl} {i : Nat} (hi : i < nMin c.l0 c.l1) (hc : c.cnt = W i)
    (hn : c.neg = W ((2 ^ 32 - nMin c.l0 c.l1 + i) % 2 ^ 32)) (hx : c.xb = W (nMain c.l0))
    (ha : c.aptr = ixApB P L g + W (256 * (i + 1))) :
    Ctr P L g (mainTop c).1 (mainTop c).2 i := by
  have hm := (nMain_bnd c.l0).2.1
  have hmin : nMin c.l0 c.l1 ≤ nMain c.l0 := Nat.min_le_left _ _
  have hw : addi c.cnt 1 = W (i + 1) := by rw [hc]; exact addi1_W (by omega)
  unfold mainTop; dsimp only
  split
  · exact (⟨hi, hw, hn, hx, ha⟩ : MainW P L g { c with cnt := addi c.cnt 1 } i)
  · rename_i h
    have hge : scmp .ge .s (W (i + 1)) (ixNmin c.l0 c.l1) = decide (nMin c.l0 c.l1 ≤ i + 1) := by
      obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
      have := rounds_lt c.l0 c.l1
      rw [(nmin_pos (by simp only [nMin] at hi; omega)).2]
      exact scmp_ge_W (by omega) (by omega)
    rw [hw, hge] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨⟨hi, hw, hn, hx, ha⟩, by dsimp only at h ⊢; omega⟩

/-- After the main loop, in block `min M R`. -/
theorem ctr_mainDone {c : IxCtl} {i : Nat} (hR : 0 < roundsOf c.l0 c.l1)
    (hi : i = nMin c.l0 c.l1) (hx : c.xb = W (nMain c.l0)) :
    Ctr P L g (ixMainDone c).1 (ixMainDone c).2 i := by
  obtain ⟨-, hr2, -⟩ := nblk_pos (tot_of_pos hR)
  obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
  have ht : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = decide (roundsOf c.l0 c.l1 ≤ nMain c.l0) := by
    rw [hx, (nmin_pos hR).1]; exact scmp_ge_W (by omega) (by omega)
  have hmin : nMin c.l0 c.l1 = min (nMain c.l0) (roundsOf c.l0 c.l1) := rfl
  unfold ixMainDone
  rw [ht]
  split
  · rename_i h
    show i = roundsOf c.l0 c.l1
    simp only [decide_eq_true_eq] at h
    omega
  · rename_i h
    simp only [decide_eq_true_eq] at h
    show nMain c.l0 < roundsOf c.l0 c.l1 ∧ i = nMain c.l0 ∧ c.xb = W (nMain c.l0)
    exact ⟨by omega, by omega, hx⟩

/-- **A skipped main loop**: no block, the barrier. -/
theorem ctr_noMain {c : IxCtl} (hx : c.xb = W (nMain c.l0))
    (h : scmpi .lt .s (ixNmin c.l0 c.l1) 1 = true) : Ctr P L g (ixNoMain c).1 (ixNoMain c).2 0 := by
  obtain ⟨h0, hge⟩ := r_zero h
  unfold ixNoMain ixMainDone
  dsimp only
  rw [hx, hge]
  exact h0.symm

/-- The main loop's entry in block 0. -/
theorem ctr_afterPre {c : IxCtl} (hx : c.xb = W (nMain c.l0)) :
    Ctr P L g (afterPre P L g c).1 (afterPre P L g c).2 0 := by
  unfold afterPre
  split
  · exact ctr_noMain hx ‹_›
  · rename_i h
    have hR : 0 < roundsOf c.l0 c.l1 := by
      cases ht : scmpi .lt .s (totL c.l0 c.l1) 64
      · exact (nblk_pos ht).1
      · exact absurd (nblk_zero ht).2.1 h
    obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
    have hmin : nMin c.l0 c.l1 = min (nMain c.l0) (roundsOf c.l0 c.l1) := rfl
    have h1 : 1 ≤ nMin c.l0 c.l1 := by have := (nMain_bnd c.l0).1; omega
    unfold mainEntry
    refine ctr_mainTop (by simp only; omega) rfl ?_ hx (addi64_eq _ (by decide))
    simp only [(nmin_pos hR).2]
    rw [neg32_W (by omega), Nat.add_zero]

/-- After the lengths, in block 0. -/
theorem ctr_lens (c : IxCtl) : Ctr P L g (ixLens c).1 (ixLens c).2 0 := by
  unfold ixLens; dsimp only
  split
  · exact ctr_noMain (eq_W _) ‹_›
  · exact (eq_W _ : ixNmain c.l0 = W (nMain c.l0))

theorem ctr_afterA (P : Params) (c : IxCtl) : Ctr P L g (ixAfterA P c).1 (ixAfterA P c).2 0 := by
  unfold ixAfterA
  split
  · exact ctr_lens c
  · trivial

/-- **The first state's counters**, in block 0. -/
theorem ctr_first {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) (g : Nat) :
    Ctr P L g (ixFirst P L g).1 (ixFirst P L g).2 0 := by
  unfold ixFirst
  simp only [batch_in hp g, Bool.false_eq_true, ite_false]
  split
  · exact ctr_afterA P _
  · trivial

/-- **The end of main block `i`**: block `i + 1`. -/
theorem ctr_mainEnd {c : IxCtl} {i : Nat} (h : MainW P L g c i) :
    Ctr P L g (mainEnd c).1 (mainEnd c).2 (i + 1) := by
  obtain ⟨hi, hc, hn, hx, ha⟩ := h
  obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
  have ha1 : addi64 c.aptr 256 = ixApB P L g + W (256 * (i + 1 + 1)) := by
    rw [ha, addi64_eq _ (by decide), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 2
  have hmin : nMin c.l0 c.l1 = min (nMain c.l0) (roundsOf c.l0 c.l1) := rfl
  have hR : 0 < roundsOf c.l0 c.l1 := by simp only [nMin] at hi; omega
  have hn1 : addi c.neg 1 = W ((2 ^ 32 - nMin c.l0 c.l1 + (i + 1)) % 2 ^ 32) := by
    rw [hn, addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  have ht : scmpi .ne .b (addi c.neg 1) 0 = decide (i + 1 ≠ nMin c.l0 c.l1) := by
    rw [hn1, scmpi_ne_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_zero, decide_eq_decide]
    simp only [nMin] at hi ⊢
    omega
  unfold mainEnd; dsimp only
  rw [ht]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    exact ctr_mainTop (by simp only; omega) hc hn1 hx ha1
  · rename_i h
    simp only [decide_eq_true_eq, not_not] at h
    exact ctr_mainDone hR h hx

/-- The extra loop's head in block `i`. -/
theorem ctr_xTop {c : IxCtl} {i : Nat} (hMR : nMain c.l0 < roundsOf c.l0 c.l1)
    (h1 : nMain c.l0 ≤ i) (h2 : i < roundsOf c.l0 c.l1) (hxb : c.xb = W i)
    (hxn : c.xn = W ((2 ^ 32 - roundsOf c.l0 c.l1 + i) % 2 ^ 32))
    (hxa : c.xa = W (((ixXa0 L g).toNat + 64 * (i - nMain c.l0)) % 2 ^ 32)) :
    Ctr P L g (xTop c).1 (xTop c).2 i := by
  have hr2 := (nblk_pos (tot_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hMR))).2.1
  have hw : addi c.xb 1 = W (i + 1) := by rw [hxb]; exact addi1_W (by omega)
  unfold xTop; dsimp only
  split
  · exact (⟨hMR, h1, h2, hw, hxn, hxa⟩ : XW L g { c with xb := addi c.xb 1 } i)
  · rename_i h
    have hge : scmp .ge .s (W (i + 1)) (ixNblk c.l0 c.l1) =
        decide (roundsOf c.l0 c.l1 ≤ i + 1) := by
      rw [(nmin_pos (by omega)).1]
      exact scmp_ge_W (by omega) (by omega)
    rw [hw, hge] at h
    simp only [decide_eq_true_eq] at h
    exact ⟨⟨hMR, h1, h2, hw, hxn, hxa⟩, by dsimp only at h ⊢; omega⟩

/-- **The extra cache's first pair**: block `M`. -/
theorem ctr_afterXpre {c : IxCtl} {i : Nat} (h : Ctr P L g .xpre c i) :
    Ctr P L g (afterXpre L g c).1 (afterXpre L g c).2 i := by
  obtain ⟨hMR, rfl, hx⟩ := h
  have hR : 0 < roundsOf c.l0 c.l1 := by omega
  obtain ⟨-, hr2, -⟩ := nblk_pos (tot_of_pos hR)
  obtain ⟨-, hm2, -⟩ := nMain_bnd c.l0
  have hnb := (nmin_pos hR).1
  have ht : scmp .ge .s c.xb (ixNblk c.l0 c.l1) = false := by
    rw [hx, hnb, scmp_ge_W (by omega) (by omega)]
    simp only [decide_eq_false_iff_not, not_le]
    exact hMR
  unfold afterXpre
  rw [ht]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ctr_xTop hMR (Nat.le_refl _) hMR hx ?_ ?_
  · simp only [hx, hnb, sub32_Wm]
    congr 1
    omega
  · have hlt : (ixXa0 L g).toNat < 2 ^ 32 := by
      simp only [ixXa0, or32, r32, truncBits, BitVec.toNat_or, BitVec.toNat_ofNat]
      exact Nat.or_lt_two_pow (by omega) (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hlt, W,
      BitVec.toNat_ofNat]
    omega

/-- **The end of extra block `i`**: block `i + 1`, or the barrier at the total. -/
theorem ctr_xEnd {c : IxCtl} {i : Nat} (h : XW L g c i) :
    Ctr P L g (xEnd c).1 (xEnd c).2 (i + 1) := by
  obtain ⟨hMR, h1, h2, hxb, hxn, hxa⟩ := h
  have hr2 := (nblk_pos (tot_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hMR))).2.1
  have hn1 : addi c.xn 1 = W ((2 ^ 32 - roundsOf c.l0 c.l1 + (i + 1)) % 2 ^ 32) := by
    rw [hxn, addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  have ht : scmpi .ne .b (addi c.xn 1) 0 = decide (i + 1 ≠ roundsOf c.l0 c.l1) := by
    rw [hn1, scmpi_ne_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_zero, decide_eq_decide]
    omega
  unfold xEnd; dsimp only
  rw [ht]
  split
  · rename_i h
    simp only [decide_eq_true_eq] at h
    refine ctr_xTop hMR (show nMain c.l0 ≤ i + 1 by omega)
      (show i + 1 < roundsOf c.l0 c.l1 by omega) hxb hn1 ?_
    rw [hxa, addi_Wm (by decide) (by decide)]
    dsimp only
    simp only [show (64 : Int).toNat = 64 from rfl]
    congr 1
    omega
  · rename_i h
    simp only [decide_eq_true_eq, not_not] at h
    exact h

/-- **A loop site is in a block below the total.** -/
theorem ctr_blk_lt {s : IxSite} {c : IxCtl} {i : Nat} (h : Ctr P L g s c i)
    (hs : s ≠ .lenA ∧ s ≠ .lenB ∧ s ≠ .pre ∧ s ≠ .xpre ∧ s ≠ .bar ∧ s ≠ .exit) :
    i < roundsOf c.l0 c.l1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  cases s <;> first
    | exact absurd rfl ‹_›
    | exact Nat.lt_of_lt_of_le h.1 (Nat.min_le_right _ _)
    | exact Nat.lt_of_lt_of_le h.1.1 (Nat.min_le_right _ _)
    | exact h.2.2.1
    | exact h.1.2.2.1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
