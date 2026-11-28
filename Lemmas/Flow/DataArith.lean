-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-! # 32-bit products and sums of truncated words

A proof tool, kernel independent: the low 32 bits of a product and a sum of words, in the form an
integer instruction computes them (`truncBits 32` of each operand), as a number modulo `2 ^ 32`. -/

namespace PTX

theorem trunc_ofNat (x : Nat) : truncBits 32 (BitVec.ofNat 64 (x % 2 ^ 32)) =
    BitVec.ofNat 64 (x % 2 ^ 32) := by
  unfold truncBits
  simp only [BitVec.toNat_ofNat]
  congr 1
  have : x % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [Nat.mod_eq_of_lt this, Nat.mod_mod]

theorem mad_trunc (x : BitVec 64) (a c : Nat) :
    truncBits 32 (truncBits 32 x * BitVec.ofNat 64 (a % 2 ^ 32) +
      BitVec.ofNat 64 (c % 2 ^ 32)) =
    BitVec.ofNat 64 ((x.toNat % 2 ^ 32 * a + c) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  unfold truncBits
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_mul]
  have h1 : x.toNat % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have h2 : a % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have h3 : c % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hm : x.toNat % 2 ^ 32 * (a % 2 ^ 32) < 2 ^ 64 := by
    calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (Nat.mod_lt _ (by norm_num))
          (Nat.mod_lt _ (by norm_num))
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hm]
  have hs : (x.toNat % 2 ^ 32 * (a % 2 ^ 32) + c % 2 ^ 32) % 2 ^ 64 % 2 ^ 32 =
      (x.toNat % 2 ^ 32 * a + c) % 2 ^ 32 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
    simp [Nat.add_mod, Nat.mul_mod]
  rw [hs]

theorem mul_trunc (a b : Nat) :
    truncBits 32 (BitVec.ofNat 64 (a % 2 ^ 32) * BitVec.ofNat 64 (b % 2 ^ 32)) =
    BitVec.ofNat 64 ((a * b) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  unfold truncBits
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  have h2 : a % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have h3 : b % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  have hm : a % 2 ^ 32 * (b % 2 ^ 32) < 2 ^ 64 := by
    calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' (Nat.mod_lt _ (by norm_num))
          (Nat.mod_lt _ (by norm_num))
      _ = 2 ^ 64 := by norm_num
  have h4 : a * b % 2 ^ 32 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt h4]
  rw [Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num) : _ < 2 ^ 64)]
  exact (Nat.mul_mod a b _).symm
end PTX

namespace PTX

theorem trunc_toNat (x : BitVec 64) : (truncBits 32 x).toNat = x.toNat % 2 ^ 32 := by
  unfold truncBits
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))

/-- The low bit of a word, shifted by six, plus an offset: the column of a half tile. -/
theorem col_chain (w : BitVec 64) (c : Nat) :
    truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 w &&&
      truncBits 32 (BitVec.ofInt 64 1)) <<< 6)) + truncBits 32 (BitVec.ofNat 64 (c % 2 ^ 32))) =
    BitVec.ofNat 64 ((64 * ((truncBits 32 w).toNat % 2) + c) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (truncBits 32 (BitVec.ofInt 64 1)).toNat = 1 := by decide
  have h3 := trunc_toNat w
  have hA : (truncBits 32 (truncBits 32 w &&& truncBits 32 (BitVec.ofInt 64 1))).toNat =
      (truncBits 32 w).toNat % 2 := by
    rw [trunc_toNat, BitVec.toNat_and, h1, Nat.and_one_is_mod]
    omega
  have hS : (truncBits 32 (truncBits 32 (truncBits 32 w &&& truncBits 32 (BitVec.ofInt 64 1))
      <<< 6)).toNat = 64 * ((truncBits 32 w).toNat % 2) := by
    rw [trunc_toNat, BitVec.toNat_shiftLeft, hA]
    omega
  have hS' : (truncBits 32 (truncBits 32 (truncBits 32 (truncBits 32 w &&&
      truncBits 32 (BitVec.ofInt 64 1)) <<< 6))).toNat = 64 * ((truncBits 32 w).toNat % 2) := by
    rw [trunc_toNat, hS]
    omega
  rw [trunc_toNat, BitVec.toNat_add, hS', trunc_toNat (BitVec.ofNat 64 _), BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- The second half tile's column is 128 on from the first's. -/
theorem add_imm128 (n : Nat) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 (n % 2 ^ 32)) +
      truncBits 32 (BitVec.ofInt 64 128)) =
    BitVec.ofNat 64 ((n + 128) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (truncBits 32 (BitVec.ofInt 64 128)).toNat = 128 := by decide
  rw [trunc_toNat, BitVec.toNat_add, trunc_toNat (BitVec.ofNat 64 _), BitVec.toNat_ofNat, h1,
    BitVec.toNat_ofNat]
  omega

end PTX
