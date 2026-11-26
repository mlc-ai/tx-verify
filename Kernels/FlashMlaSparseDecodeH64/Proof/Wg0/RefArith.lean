-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ref

@[expose] public section

/-! # Warpgroup 0's loop words

The block count of the two lengths (`rounds_range`), the counter's first word (`cnt_init`), and
the words after block `r` (`words_next`, `cnt_next`): the rings' slots and parities of block
`r + 1`, and the counter's test of the last block. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

theorem r15_range {x : BitVec 64} (hx : x.toNat < 2 ^ 32) (h : scmpi .lt .s x 64 = false) :
    64 ≤ x.toNat ∧ x.toNat < 2 ^ 31 := by
  simp only [scmpi, PTX.compare, r32, truncBits, i32, toSigned, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, decide_eq_false_iff_not] at h
  split_ifs at h <;> omega

/-- **The block count**: a padded total of at least 64 gives between 1 and `2 ^ 25` blocks, the
word of `nblk`. -/
theorem rounds_range {l0 l1 : BitVec 64} (h : scmpi .lt .s (r15 l0 l1) 64 = false) :
    1 ≤ rounds l0 l1 ∧ rounds l0 l1 < 2 ^ 26 ∧ nblk l0 l1 = W (rounds l0 l1) := by
  have hx : (r15 l0 l1).toNat < 2 ^ 32 := by
    simp only [r15, add32, truncBits, BitVec.toNat_ofNat]; omega
  obtain ⟨h1, h2⟩ := r15_range hx h
  have hw : r15 l0 l1 = W (r15 l0 l1).toNat := by simp [W]
  have hn : nblk l0 l1 = W ((r15 l0 l1).toNat / 64) := by
    unfold nblk
    rw [hw]
    w32_norm
  simp only [rounds, h, Bool.false_eq_true, ↓reduceIte, hn]
  rw [toNat_W (by omega)]
  exact ⟨by omega, by omega, rfl⟩

theorem addi1_W {x : Nat} (hx : x < 2 ^ 32) : addi (W x) 1 = W ((x + 1) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

/-- The counter's first word: `1 - R`. -/
theorem cnt_init {R : Nat} (h1 : 1 ≤ R) (hR : R < 2 ^ 26) :
    sub32 (i32 1) (W R) = W ((2 ^ 32 + 1 + 0 - R) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub32, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_sub,
    BitVec.toNat_ofInt]
  omega

/-- **The counter after block `r`**: the test of the last block, and the next word. -/
theorem cnt_next {r R : Nat} (hr : r < R) (hR : R < 2 ^ 26) :
    scmpi .eq .b (W ((2 ^ 32 + 1 + r - R) % 2 ^ 32)) 0 = decide (r + 1 = R) ∧
      addi (W ((2 ^ 32 + 1 + r - R) % 2 ^ 32)) 1 = W ((2 ^ 32 + 1 + (r + 1) - R) % 2 ^ 32) ∧
      scmpi .ne .b (W ((2 ^ 32 + 1 + (r + 1) - R) % 2 ^ 32)) 1 = decide (r + 1 ≠ R) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [scmpi_eq_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_zero, decide_eq_decide]
    omega
  · rw [addi1_W (by omega)]
    congr 1
    omega
  · rw [scmpi_ne_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_one, decide_eq_decide]
    omega

theorem nvs_W {v : Nat} (hv : v < 4) : nvs (W v) = W ((v + 1) % 4) := by
  interval_cases v <;> decide

theorem npv_W {v q : Nat} (hv : v < 4) (hq : q < 2) :
    npv (W v) (W q) = W (if v = 3 then 1 - q else q) := by
  interval_cases v <;> interval_cases q <;> decide

theorem nsl_W {h : Nat} (hh : h < 2) : andi (not32 (W h)) 1 = W (1 - h) := by
  interval_cases h <;> decide

theorem nps_W {h q : Nat} (hh : h < 2) (hq : q < 2) :
    nps (W h) (W q) = W (if h = 1 then 1 - q else q) := by
  interval_cases h <;> interval_cases q <;> decide

/-- **The rings' words after block `r`** are block `r + 1`'s. -/
theorem words_next (r : Nat) :
    nvs (W (r % 4)) = W ((r + 1) % 4) ∧ npv (W (r % 4)) (W (r / 4 % 2)) = W ((r + 1) / 4 % 2) ∧
      andi (not32 (W (r % 2))) 1 = W ((r + 1) % 2) ∧
      nps (W (r % 2)) (W (r / 2 % 2)) = W ((r + 1) / 2 % 2) := by
  rw [nvs_W (by omega), npv_W (by omega) (by omega), nsl_W (by omega), nps_W (by omega) (by omega)]
  refine ⟨by congr 1; omega, ?_, by congr 1; omega, ?_⟩
  · congr 1
    split_ifs <;> omega
  · congr 1
    split_ifs <;> omega

theorem bi_next {r : Nat} (hr : r < 2 ^ 26) : addi (W (r + 1)) 1 = W (r + 1 + 1) := by
  rw [addi1_W (by omega)]
  congr 1
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
