-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Word
public import Lemmas.Flow.Arith32Wide

@[expose] public section

/-! # More of the code's 32-bit arithmetic on small words

A proof tool (FlashMLA request G17), beside `Arith32Word.lean`, for the forms of
`Arith32Wide.lean`: the signed maximum of two small words is their maximum (`max32_W`), and the
wrapping negation and subtraction of words are the differences modulo `2 ^ 32` (`neg32_W`,
`sub32_W_mod`); a mask `-(2 ^ k)` rounds a word down to a multiple of `2 ^ k` (`andi_W_negpow`), so
a ring slot's update `(s + 1) - ((s + 1) & -4)` is `(s + 1) % 4` (`slot_update_W`). -/

namespace PTX.Flow.Arith32
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem max32_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    max32 (W a) (W b) = W (max a b) := by
  have hg : compare .gt .s 32 (W a) (W b) = decide (a > b) := by
    have := scmp_gt_W ha hb
    simpa [scmp, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega)] using this
  simp only [max32, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega), hg]
  by_cases h : a > b
  · simp only [h, decide_true, ↓reduceIte, Nat.max_eq_left (Nat.le_of_lt h)]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      Nat.max_eq_right (Nat.le_of_not_lt h)]

/-- **The wrapping negation of a word** is its difference from `2 ^ 32`, modulo `2 ^ 32`. -/
theorem neg32_W {a : Nat} (ha : a < 2 ^ 32) : neg32 (W a) = W ((2 ^ 32 - a) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [neg32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_neg]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega)]
  omega

/-- **The wrapping subtraction of two words**, modulo `2 ^ 32`. -/
theorem sub32_W_mod {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    sub32 (W a) (W b) = W ((a + 2 ^ 32 - b) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_sub]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega)]
  omega

/-- A mask that clears the low `k` bits of a 32-bit number rounds it down to a multiple of
`2 ^ k`. -/
theorem and_negpow {a k : Nat} (ha : a < 2 ^ 32) (hk : k ≤ 32) :
    a &&& (2 ^ 32 - 2 ^ k) = a - a % 2 ^ k := by
  have h1 : 2 ^ 32 - 2 ^ k = (2 ^ (32 - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hk]
  have h2 : a - a % 2 ^ k = (a / 2 ^ k) <<< k := by
    rw [Nat.shiftLeft_eq]
    have := Nat.div_add_mod a (2 ^ k)
    rw [Nat.mul_comm] at this
    omega
  rw [h1, h2]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases hik : i ≥ k
  · rw [Nat.sub_add_cancel hik]
    by_cases hi : i < 32
    · simp [hik, show i - k < 32 - k by omega]
    · have : a.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [hik, this]
  · simp [hik]

/-- **A word and the mask `-(2 ^ k)`** is the word rounded down to a multiple of `2 ^ k`. -/
theorem andi_W_negpow {a k : Nat} (ha : a < 2 ^ 32) (hk : k < 32) :
    andi (W a) (-(2 ^ k : Nat) : Int) = W (a - a % 2 ^ k) := by
  have hm : (i32 (-(2 ^ k : Nat) : Int)).toNat = 2 ^ 32 - 2 ^ k := by
    have hp : 2 ^ k < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hk
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have h64 : ((-(2 ^ k : Nat) : Int) % (2 ^ 64 : Nat)).toNat = 2 ^ 64 - 2 ^ k := by
      have hp' : (2 ^ k : Nat) < 2 ^ 64 := by
        exact lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by norm_num))
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      generalize 2 ^ k = n at hp' hpos ⊢
      omega
    rw [h64]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    generalize 2 ^ k = n at hp hpos ⊢
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [andi, r32_W ha, BitVec.toNat_and, W, BitVec.toNat_ofNat]
  rw [hm, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), and_negpow ha hk.le]
  have : a - a % 2 ^ k < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

/-- **A ring slot's update**: `(s + 1) - ((s + 1) & -4)` is `(s + 1) % 4`. -/
theorem slot_update_W {a : Nat} (ha : a < 2 ^ 32) :
    sub32 (W a) (andi (W a) (-(2 ^ 2 : Nat) : Int)) = W (a % 4) := by
  rw [andi_W_negpow ha (by norm_num), sub32_W (Nat.sub_le _ _) ha]
  congr 1
  have : a % 2 ^ 2 ≤ a := Nat.mod_le _ _
  norm_num at this ⊢
  omega

end

end PTX.Flow.Arith32
