-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ref
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # Warpgroup 2's block counter

The block count of a padded total of at least 64 (`blocks_pos`: between `1` and `2 ^ 26`, and the
counter's first word `-R`), and the counter after block `i` (`cnt_next`): the next block's word,
and the back-edge's test is `i + 1 ≠ R`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

/-- A 32-bit word whose signed value is at least 64 is a word in `[64, 2 ^ 31)`. -/
theorem word_ge64 {x : BitVec 64} (hx : x.toNat < 2 ^ 32) (h : scmpi .lt .s x 64 = false) :
    64 ≤ x.toNat ∧ x.toNat < 2 ^ 31 := by
  simp only [scmpi, PTX.compare, r32, truncBits, i32, toSigned, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, decide_eq_false_iff_not] at h
  split_ifs at h <;> omega

/-- **The block count** of a padded total of at least 64, and the counter's first word. -/
theorem blocks_pos {l0 l1 : BitVec 64} (h : scmpi .lt .s (r57 l0 l1) 64 = false) :
    1 ≤ rounds l0 l1 ∧ rounds l0 l1 < 2 ^ 26 ∧
      neg32 (nblk l0 l1) = W ((2 ^ 32 - rounds l0 l1 + 0) % 2 ^ 32) := by
  have hx : (r57 l0 l1).toNat < 2 ^ 32 := by
    simp only [r57, add32, truncBits, BitVec.toNat_ofNat]; omega
  obtain ⟨h1, h2⟩ := word_ge64 hx h
  have hn : nblk l0 l1 = W ((r57 l0 l1).toNat / 64) := by
    unfold nblk
    rw [show r57 l0 l1 = W (r57 l0 l1).toNat by simp [W]]
    w32_norm
  simp only [rounds, h, Bool.false_eq_true, ↓reduceIte, hn]
  rw [toNat_W (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [neg32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_neg]
  omega

/-- **The counter after block `i`** of `R`: block `i + 1`'s word, and the back-edge is taken
exactly when `i + 1 ≠ R`. -/
theorem cnt_next {i R : Nat} (hr : i < R) (hR : R < 2 ^ 26) :
    addi (W ((2 ^ 32 - R + i) % 2 ^ 32)) 1 = W ((2 ^ 32 - R + (i + 1)) % 2 ^ 32) ∧
      scmpi .ne .b (addi (W ((2 ^ 32 - R + i) % 2 ^ 32)) 1) 0 = decide (i + 1 ≠ R) := by
  have ha : addi (W ((2 ^ 32 - R + i) % 2 ^ 32)) 1 = W ((2 ^ 32 - R + (i + 1)) % 2 ^ 32) := by
    rw [addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  refine ⟨ha, ?_⟩
  rw [ha, scmpi_ne_b_W (by omega) (by omega) (by omega)]
  simp only [Int.toNat_zero, decide_eq_decide]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
