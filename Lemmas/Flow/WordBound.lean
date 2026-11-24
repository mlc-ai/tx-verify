-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # Bounds on the code's 32-bit words

The code's 32-bit operations (`Lemmas/Flow/Arith32.lean`) on words that are not known exactly:
an addition is at most the sum of its operands, a mask at most the mask, a left shift the product
modulo `2 ^ 32`, an `or` of a word below `2 ^ k` with a multiple of `2 ^ k` their sum; and the
signed value (`toSigned 32`) of an addition of an immediate and of a subtraction when no wrap
occurs. Promoted from tml-fa4's `Proof2/Lib/WordBound.lean` (lane T1). -/

namespace PTX.Flow.Arith32
open PTX PTX.Proof PTX.Flow

theorem toNat_r32_lt (x : BitVec 64) : (r32 x).toNat < 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem r32_of_lt {x : BitVec 64} (h : x.toNat < 2 ^ 32) : r32 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem toNat_add32_le (x y : BitVec 64) :
    (add32 x y).toNat ≤ (r32 x).toNat + (r32 y).toNat := by
  simp only [add32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  have := toNat_r32_lt x
  have := toNat_r32_lt y
  omega

theorem toNat_add32_lt (x y : BitVec 64) : (add32 x y).toNat < 2 ^ 32 := by
  simp only [add32, truncBits, BitVec.toNat_ofNat]; omega

theorem toNat_andi_le (x : BitVec 64) (n : Int) : (andi x n).toNat ≤ (i32 n).toNat := by
  simp only [andi, BitVec.toNat_and]
  exact Nat.and_le_right

/-- A left shift by `k < 32` is the product by `2 ^ k` modulo `2 ^ 32`. -/
theorem toNat_shl {k : Nat} (x : BitVec 64) (hk : k < 32) :
    (shl x (k : Int)).toNat = (r32 x).toNat * 2 ^ k % 2 ^ 32 := by
  have h : (i32 (k : Int)).toNat = k := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  show (if (i32 (k : Int)).toNat ≥ 32 then 0
    else truncBits 32 (r32 x <<< (i32 (k : Int)).toNat)).toNat = _
  rw [h, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  generalize x.toNat % 2 ^ 32 % 2 ^ 64 * 2 ^ k = t
  omega

/-- An `or` of a word below `2 ^ k` with a multiple of `2 ^ k` is their sum. -/
theorem toNat_or32_add {k : Nat} {x y : BitVec 64} (hx : (r32 x).toNat < 2 ^ k)
    (hy : (r32 y).toNat % 2 ^ k = 0) :
    (r32 x ||| r32 y).toNat = (r32 x).toNat + (r32 y).toNat := by
  rw [BitVec.toNat_or]
  have hq : (r32 y).toNat = 2 ^ k * ((r32 y).toNat / 2 ^ k) := by
    have := Nat.div_add_mod (r32 y).toNat (2 ^ k); omega
  rw [hq, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

theorem toSigned32_spec (x : BitVec 64) :
    toSigned 32 x % 2 ^ 32 = ((x.toNat % 2 ^ 32 : Nat) : Int) ∧ -2 ^ 31 ≤ toSigned 32 x ∧
      toSigned 32 x < 2 ^ 31 := by
  simp only [toSigned]
  have h := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  split <;> omega

/-- A word with a nonnegative signed value is that value. -/
theorem toNat_r32_of_toSigned {x : BitVec 64} (h : 0 ≤ toSigned 32 x) :
    ((r32 x).toNat : Int) = toSigned 32 x := by
  have := toSigned32_spec x
  simp only [toSigned] at h this ⊢
  simp only [r32, truncBits, BitVec.toNat_ofNat]
  split at h <;> split <;> omega

theorem toSigned_addi (x : BitVec 64) (n : Int) (h0 : -2 ^ 31 ≤ toSigned 32 x + n)
    (h1 : toSigned 32 x + n < 2 ^ 31) : toSigned 32 (addi x n) = toSigned 32 x + n := by
  have h1' := toSigned32_spec (addi x n)
  have h2 := toSigned32_spec x
  have h3 : ((addi x n).toNat : Int) % 2 ^ 32 = ((x.toNat : Int) + n) % 2 ^ 32 := by
    simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
      BitVec.toNat_ofInt]
    omega
  omega

theorem toSigned_sub32 (x y : BitVec 64) (h0 : -2 ^ 31 ≤ toSigned 32 x - toSigned 32 y)
    (h1 : toSigned 32 x - toSigned 32 y < 2 ^ 31) :
    toSigned 32 (sub32 x y) = toSigned 32 x - toSigned 32 y := by
  have h1' := toSigned32_spec (sub32 x y)
  have h2 := toSigned32_spec x
  have h2' := toSigned32_spec y
  have h3 : ((sub32 x y).toNat : Int) % 2 ^ 32 = ((x.toNat : Int) - y.toNat) % 2 ^ 32 := by
    simp only [sub32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_sub]
    omega
  omega

end PTX.Flow.Arith32
