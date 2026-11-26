-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexVal
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Arith32Norm
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The index warp's block counts

The code's three counts of two length words `l0`, `l1` (`Lib/IndexVal.lean`): the main cache's
blocks `ixNmain l0` (`nMain`, between 1 and `2 ^ 25`: the padded length is at least 64), the
total `ixNblk l0 l1` and the main loop's `ixNmin l0 l1`, the signed minimum. The total is the
CTA's block count `roundsOf l0 l1` (`Lib/Rounds.lean`) when the padded total is at least 64
(`nblk_pos`); otherwise it is not positive as a signed word, so the main loop is skipped and the
extra loop's test fails at once (`nblk_zero`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- **The main cache's block count** of a length word. -/
def nMain (l0 : BitVec 64) : Nat := (ixNmain l0).toNat

/-- The main loop's block count: the smaller of the main cache's and the total. -/
abbrev nMin (l0 l1 : BitVec 64) : Nat := min (nMain l0) (roundsOf l0 l1)

private theorem trunc_lt (x : BitVec 64) : (truncBits 32 x).toNat < 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]; omega

/-- A 32-bit word whose signed value is above 64 lies between 64 and `2 ^ 31`. -/
private theorem gt64 {x : BitVec 64} (hx : x.toNat < 2 ^ 32)
    (h : PTX.compare .gt .s 32 x (r32 (i32 64)) = true) : 64 < x.toNat ∧ x.toNat < 2 ^ 31 := by
  have h64 : r32 (i32 64) = W 64 := by decide
  rw [h64] at h
  simp only [PTX.compare, toSigned, toNat_W (show 64 < 2 ^ 64 by omega),
    decide_eq_true_eq] at h
  split_ifs at h <;> omega

/-- **The main cache's blocks**: between 1 and `2 ^ 25`. -/
theorem nMain_bnd (l0 : BitVec 64) :
    1 ≤ nMain l0 ∧ nMain l0 < 2 ^ 25 ∧ ixNmain l0 = W (nMain l0) := by
  refine ⟨?_, ?_, eq_W _⟩ <;>
  · have hv : 64 ≤ (ixMax l0).toNat ∧ (ixMax l0).toNat < 2 ^ 31 := by
      simp only [ixMax, max32]
      split
      · rename_i h
        have := gt64 (x := r32 (ixPad l0)) (trunc_lt _) h
        omega
      · decide
    have hm : ixMax l0 = W (ixMax l0).toNat := eq_W _
    unfold nMain ixNmain
    rw [hm, shru_int (by omega) (by omega) (by omega)]
    simp only [Int.reduceToNat, Nat.reducePow]
    rw [toNat_W (by omega)]
    omega

/-- The total word of two lengths. -/
theorem tot_eq (l0 l1 : BitVec 64) : ixTot l0 l1 = totL l0 l1 := rfl
theorem nblk_eq (l0 l1 : BitVec 64) : ixNblk l0 l1 = nblkL l0 l1 := rfl

/-- A 32-bit word whose signed value is at least 64. -/
private theorem sge64 {a : Nat} (hx : a < 2 ^ 32) (h : scmpi .lt .s (W a) 64 = false) :
    64 ≤ a ∧ a < 2 ^ 31 := by
  have h64 : (i32 64) = W 64 := by decide
  simp only [scmpi, PTX.compare, r32_W hx, h64, toSigned, toNat_W (show a < 2 ^ 64 by omega),
    toNat_W (show 64 < 2 ^ 64 by omega), decide_eq_false_iff_not] at h
  split_ifs at h <;> omega

/-- **A padded total of at least 64**: the total is the block count, between 1 and `2 ^ 25`. -/
theorem nblk_pos {l0 l1 : BitVec 64} (h : scmpi .lt .s (totL l0 l1) 64 = false) :
    1 ≤ roundsOf l0 l1 ∧ roundsOf l0 l1 < 2 ^ 25 ∧ ixNblk l0 l1 = W (roundsOf l0 l1) := by
  have hx : (totL l0 l1).toNat < 2 ^ 32 := trunc_lt _
  have ht : totL l0 l1 = W (totL l0 l1).toNat := eq_W _
  have hb : 64 ≤ (totL l0 l1).toNat ∧ (totL l0 l1).toNat < 2 ^ 31 := by
    rw [ht] at h
    generalize (totL l0 l1).toNat = a at h hx ⊢
    exact sge64 hx h
  have hn : nblkL l0 l1 = W ((totL l0 l1).toNat / 64) := by
    unfold nblkL
    rw [ht]
    w32_norm
  have hR : roundsOf l0 l1 = (totL l0 l1).toNat / 64 := by
    simp only [roundsOf, h, Bool.false_eq_true, ↓reduceIte, hn]
    exact toNat_W (by omega)
  rw [hR, nblk_eq, hn]
  exact ⟨by omega, by omega, rfl⟩

/-- An arithmetic shift of a negative word stays negative. -/
private theorem shrs_neg {b : Nat} (h1 : 2 ^ 31 ≤ b) (h2 : b < 2 ^ 32) (k : Nat) (hk : k < 32) :
    2 ^ 31 ≤ (shrs (W b) k).toNat := by
  have hs : toSigned 32 (r32 (W b)) = (b : Int) - 2 ^ 32 := by
    simp only [toSigned, r32_W h2, toNat_W (show b < 2 ^ 64 by omega)]
    simp only [show b % 2 ^ 32 = b by omega, show ¬ b < 2 ^ (32 - 1) by omega, ↓reduceIte]
  have hi : (i32 (k : Int)).toNat = k := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [shrs]
  rw [hs, hi, Nat.min_eq_left (Nat.le_of_lt hk)]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have hp : (0 : Int) < 2 ^ k := by positivity
  have hq : ((b : Int) - 2 ^ 32) / 2 ^ k < 0 := Int.ediv_neg_of_neg_of_pos (by omega) hp
  have hq2 : -2 ^ 31 ≤ ((b : Int) - 2 ^ 32) / 2 ^ k := by
    rw [Int.le_ediv_iff_mul_le hp]
    have : (1 : Int) ≤ 2 ^ k := by omega
    nlinarith
  omega

/-- The sign word of a negative word. -/
private theorem shrs31_neg {b : Nat} (h1 : 2 ^ 31 ≤ b) (h2 : b < 2 ^ 32) :
    shrs (W b) 31 = W (2 ^ 32 - 1) := by
  have hs : toSigned 32 (r32 (W b)) = (b : Int) - 2 ^ 32 := by
    simp only [toSigned, r32_W h2, toNat_W (show b < 2 ^ 64 by omega)]
    simp only [show b % 2 ^ 32 = b by omega, show ¬ b < 2 ^ (32 - 1) by omega, ↓reduceIte]
  have hi : (i32 (31 : Int)).toNat = 31 := by decide
  simp only [shrs]
  rw [hs, hi]
  apply BitVec.eq_of_toNat_eq
  have hq : ((b : Int) - 2 ^ 32) / 2 ^ min 31 32 = -1 := by
    show ((b : Int) - 2 ^ 32) / 2147483648 = -1
    omega
  rw [hq]
  decide

/-- **A padded total below 64**: the total is not positive as a signed word, so the main loop's
test `< 1` holds and the extra loop's test `xb ≥ total` holds for the main cache's blocks. -/
theorem nblk_zero {l0 l1 : BitVec 64} (h : scmpi .lt .s (totL l0 l1) 64 = true) :
    roundsOf l0 l1 = 0 ∧ scmpi .lt .s (ixNmin l0 l1) 1 = true ∧
      scmp .ge .s (W (nMain l0)) (ixNblk l0 l1) = true := by
  obtain ⟨hm1, hm2, hm⟩ := nMain_bnd l0
  refine ⟨by simp only [roundsOf, h, ↓reduceIte], ?_⟩
  have hx : (totL l0 l1).toNat < 2 ^ 32 := trunc_lt _
  have ht : totL l0 l1 = W (totL l0 l1).toNat := eq_W _
  -- the total's word `v`: 0, or a negative word
  obtain ⟨v, hv, hneg⟩ : ∃ v, ixNblk l0 l1 = W v ∧ (v = 0 ∨ 2 ^ 31 ≤ v ∧ v < 2 ^ 32) := by
    rw [nblk_eq]
    unfold nblkL
    generalize (totL l0 l1).toNat = a at ht hx
    rw [ht]
    by_cases ha : a < 2 ^ 31
    · have ha64 : a < 64 := by
        rw [ht] at h
        simp only [scmpi, PTX.compare, r32_W hx, toSigned, toNat_W (show a < 2 ^ 64 by omega),
          decide_eq_true_eq] at h
        have : (i32 64) = W 64 := by decide
        simp only [this, toNat_W (show 64 < 2 ^ 64 by omega)] at h
        split_ifs at h <;> omega
      refine ⟨0, ?_, .inl rfl⟩
      w32_norm
    · rw [shrs31_neg (by omega) hx]
      have h63 : shru (W (2 ^ 32 - 1)) 26 = W 63 := by w32_norm
      rw [h63, add32_Wm]
      generalize hb : (a % 2 ^ 32 + 63 % 2 ^ 32) % 2 ^ 32 = b
      by_cases hb2 : b < 2 ^ 31
      · refine ⟨0, ?_, .inl rfl⟩
        w32_norm
      · refine ⟨_, eq_W _, .inr ⟨shrs_neg (by omega) (by omega) 6 (by omega), trunc_lt _⟩⟩
  rw [hv]
  have hM := hm1
  rcases hneg with rfl | ⟨hv1, hv2⟩
  · simp only [ixNmin, hm, hv]
    w32_norm
    simp
  · have hmn : min32 (W (nMain l0)) (W v) = W v := by
      simp only [min32, r32_W hv2, r32_W (show nMain l0 < 2 ^ 32 by omega), PTX.compare, toSigned,
        toNat_W (show v < 2 ^ 64 by omega), toNat_W (show nMain l0 < 2 ^ 64 by omega),
        Nat.reduceSub, Nat.reducePow, decide_eq_true_eq]
      split_ifs <;> first | rfl | omega
    simp only [ixNmin, hm, hv, hmn]
    have h1 : (i32 1) = W 1 := by decide
    simp only [scmpi, scmp, PTX.compare, r32_W hv2, r32_W (show nMain l0 < 2 ^ 32 by omega), h1,
      toSigned, toNat_W (show v < 2 ^ 64 by omega), toNat_W (show nMain l0 < 2 ^ 64 by omega),
      toNat_W (show 1 < 2 ^ 64 by omega), Nat.reduceSub, Nat.reducePow]
    split_ifs <;> simp <;> omega

/-- A positive block count: the padded total is at least 64. -/
theorem tot_of_pos {l0 l1 : BitVec 64} (h : 0 < roundsOf l0 l1) :
    scmpi .lt .s (totL l0 l1) 64 = false := by
  cases ht : scmpi .lt .s (totL l0 l1) 64
  · rfl
  · simp [roundsOf, ht] at h

/-- **The main loop's count word** for a positive block count. -/
theorem nmin_pos {l0 l1 : BitVec 64} (h : 0 < roundsOf l0 l1) :
    ixNblk l0 l1 = W (roundsOf l0 l1) ∧ ixNmin l0 l1 = W (nMin l0 l1) := by
  obtain ⟨-, hr2, hr⟩ := nblk_pos (tot_of_pos h)
  obtain ⟨-, hm2, hm⟩ := nMain_bnd l0
  refine ⟨hr, ?_⟩
  simp only [ixNmin, hm, hr]
  exact min32_W (by omega) (by omega)

/-- **The main loop is skipped only for no block.** -/
theorem r_zero {l0 l1 : BitVec 64} (h : scmpi .lt .s (ixNmin l0 l1) 1 = true) :
    roundsOf l0 l1 = 0 ∧ scmp .ge .s (W (nMain l0)) (ixNblk l0 l1) = true := by
  cases ht : scmpi .lt .s (totL l0 l1) 64
  · obtain ⟨hr1, hr2, -⟩ := nblk_pos ht
    obtain ⟨hm1, hm2, -⟩ := nMain_bnd l0
    rw [(nmin_pos (by omega)).2] at h
    simp only [nMin] at h
    w32_norm at h
    simp only [decide_eq_true_eq] at h
    exfalso
    omega
  · obtain ⟨h1, -, h3⟩ := nblk_zero ht
    exact ⟨h1, h3⟩

/-- **The block count is below `2 ^ 25`.** -/
theorem rounds_lt (l0 l1 : BitVec 64) : roundsOf l0 l1 < 2 ^ 25 := by
  cases ht : scmpi .lt .s (totL l0 l1) 64
  · exact (nblk_pos ht).2.1
  · rw [(nblk_zero ht).1]; decide

/-- The negation of a word. -/
theorem neg32_W {a : Nat} (ha : a < 2 ^ 32) : neg32 (W a) = W ((2 ^ 32 - a) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [neg32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_neg]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
