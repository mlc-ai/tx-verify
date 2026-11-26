-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The TMA warp's block words

The block count of a padded total of at least 64 (`blocks_pos`) and the words of the loop's end
(`block_end`): the counter, the two slots, the two parity words and the negative counter after
block `r` are block `r + 1`'s, and the loop goes on exactly when `r + 1` is below the block count.
The slots and parities are decided on the four values of `r % 4` (`slot_step`, `tile_step`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The quotient by 64 of a word between 64 and `2 ^ 31`, as the code computes it. -/
theorem div64_word (x : Nat) (h1 : 64 ≤ x) (h2 : x < 2 ^ 31) :
    shrs (add32 (W x) (shru (shrs (W x) 31) 26)) 6 = W (x / 64) := by
  w32_norm

/-- A 32-bit word whose signed value is at least 64 lies between 64 and `2 ^ 31`. -/
theorem word_ge64 {x : BitVec 64} (hx : x.toNat < 2 ^ 32) (h : scmpi .lt .s x 64 = false) :
    64 ≤ x.toNat ∧ x.toNat < 2 ^ 31 := by
  simp only [scmpi, PTX.compare, r32, truncBits, i32, toSigned, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, decide_eq_false_iff_not] at h
  split_ifs at h <;> omega

/-- **The block count**: a padded total of at least 64 gives between 1 and `2 ^ 25` blocks, and
the negative counter's first word. -/
theorem blocks_pos {l0 l1 : BitVec 64} (h : scmpi .lt .s (tot l0 l1) 64 = false) :
    1 ≤ rounds l0 l1 ∧ rounds l0 l1 < 2 ^ 26 ∧
      neg32 (nblk l0 l1) = W ((2 ^ 32 - rounds l0 l1) % 2 ^ 32) := by
  have hx : (tot l0 l1).toNat < 2 ^ 32 := by
    simp only [tot, add32, truncBits, BitVec.toNat_ofNat]; omega
  have hb := word_ge64 hx h
  have hq := div64_word _ hb.1 hb.2
  rw [← eq_W] at hq
  have hn : nblk l0 l1 = W ((tot l0 l1).toNat / 64) := hq
  have hR : rounds l0 l1 = (tot l0 l1).toNat / 64 := by
    simp only [rounds, h, Bool.false_eq_true, ↓reduceIte, hn]
    exact toNat_W (by omega)
  rw [hR, hn]
  refine ⟨by omega, by omega, BitVec.eq_of_toNat_eq ?_⟩
  simp only [neg32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_neg]
  omega

/-- The ring's slot and parity after a block, on slot `a` and parity `q`. -/
theorem slot_step (a q : Nat) (ha : a < 4) (hq : q < 2) :
    slotNext (W a) = W ((a + 1) % 4) ∧
      sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 (W q) 255))
        (truncBits 16 (sel (scmpi .eq .b (W a) 3) (i16 1) (i16 0)))) (i16 1) (i16 0) =
        W (if a = 3 then 1 - q else q) := by
  interval_cases a <;> interval_cases q <;> decide

/-- The tile's slot and parity after a block, on block `a` of four. -/
theorem tile_step (a : Nat) (ha : a < 4) :
    andi (not32 (W (a % 2))) 1 = W ((a + 1) % 2) ∧
      sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 (W (a / 2)) 255))
        (truncBits 16 (andi16 (truncBits 16 (r32 (W (a % 2)))) 255))) (i16 1) (i16 0) =
        W ((a + 1) / 2 % 2) := by
  interval_cases a <;> decide

/-- **The words after block `r`** of `R`: block `r + 1`'s, and the loop's test. -/
theorem block_end {d : D} {r R : Nat} (hr : r < R) (hR : R < 2 ^ 26) (hc : d.cnt = W r)
    (hb : d.buf = W (r % 2)) (hs : d.slot = W (r % 4)) (hf : d.pf = W (r / 2 % 2))
    (hq : d.pr = W (r / 4 % 2)) (hn : d.neg = W ((2 ^ 32 - R + r) % 2 ^ 32)) :
    addi d.cnt 1 = W (r + 1) ∧ andi (not32 d.buf) 1 = W ((r + 1) % 2) ∧
      slotNext d.slot = W ((r + 1) % 4) ∧ pfNext d = W ((r + 1) / 2 % 2) ∧
      prNext d = W ((r + 1) / 4 % 2) ∧ addi d.neg 1 = W ((2 ^ 32 - R + (r + 1)) % 2 ^ 32) ∧
      scmpi .ne .b (addi d.neg 1) 0 = decide (r + 1 ≠ R) := by
  have h4 : r % 4 < 4 := Nat.mod_lt _ (by omega)
  obtain ⟨hs1, hs2⟩ := slot_step (r % 4) (r / 4 % 2) h4 (Nat.mod_lt _ (by omega))
  obtain ⟨ht1, ht2⟩ := tile_step (r % 4) h4
  have e2 : r % 2 = r % 4 % 2 := by omega
  have e3 : r / 2 % 2 = r % 4 / 2 := by omega
  have hneg : addi d.neg 1 = W ((2 ^ 32 - R + (r + 1)) % 2 ^ 32) := by
    rw [hn, addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, hneg, ?_⟩
  · rw [hc, show ((1 : Int)) = ((1 : Nat) : Int) from rfl, addi_W (by omega) (by omega)]
  · rw [hb, e2, ht1]; congr 1; omega
  · rw [hs, hs1]; congr 1; omega
  · unfold pfNext
    rw [hf, hb, e2, e3, ht2]; congr 1; omega
  · unfold prNext
    rw [hq, hs, hs2]; congr 1; split_ifs <;> omega
  · rw [hneg, scmpi_ne_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_zero, decide_eq_decide]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
