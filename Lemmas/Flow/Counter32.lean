-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32

@[expose] public section

/-! # Loop counters on 32-bit words

A proof tool, generic over the kernel (promoted from the tml-fa4 softmax warps' round counters).

A counter that the code steps by `add.s32 … 1` and tests against a constant with `setp.ne` is
the word `i32 x` of an integer `x`; its step is `i32 (x + 1)` and its test is `x ≠ c` as long as
`x` stays within one period of the words. A trip count read from a word is its two's complement
value `toSigned 32`, and the code's `setp.lt.s32 … 1` reads that value. Also: word differences
read back (`sub32_swap`) and a parity word flipped by `xor.b32 … 1` (`xor_par`).

No other library module imports it, because a kernel that opens `PTX.Flow.Arith32` and keeps its
own lemma of one of these names would see two candidates; such a kernel deletes its copy and
imports this module. -/

namespace PTX.Flow.Arith32
open PTX

theorem i32_addi (x : Int) : addi (i32 x) 1 = i32 (x + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

theorem toSigned_r32 (x : BitVec 64) :
    -2 ^ 31 ≤ toSigned 32 (r32 x) ∧ toSigned 32 (r32 x) < 2 ^ 31 := by
  simp only [toSigned, r32, truncBits, BitVec.toNat_ofNat]
  split_ifs <;> omega

/-- A word is the word of its two's complement value. -/
theorem i32_toSigned (x : BitVec 64) : r32 x = i32 (toSigned 32 (r32 x)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [toSigned, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  split_ifs <;> omega

/-- The bits of a negative counter at least one step before `-1`: its increment does not wrap
(a bound for a measure that ranks a loop by its counter). -/
theorem i32_room {x : Int} (h1 : -2 ^ 32 < x) (h2 : x ≤ -2) : (r32 (i32 x)).toNat + 1 < 2 ^ 32 := by
  simp only [r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- The bits of a counter's increment, when the counter is not the last word. -/
theorem r32_addi1 {t : BitVec 64} (h : (r32 t).toNat + 1 < 2 ^ 32) :
    (r32 (addi t 1)).toNat = (r32 t).toNat + 1 := by
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt] at h ⊢
  omega

/-- A two's complement value of 32 bits is below `2 ^ 31`. -/
theorem toSigned32_lt (x : BitVec 64) : toSigned 32 x < 2 ^ 31 := by
  unfold toSigned
  simp only
  split <;> omega

/-- The test `setp.ne … -1` of a negative counter. -/
theorem ne_m1 {x : Int} (h1 : -2 ^ 32 < x) (h2 : x ≤ 0) :
    scmpi .ne .b (i32 x) (-1) = true ↔ x ≠ -1 := by
  simp only [scmpi, PTX.compare, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    decide_eq_true_eq, ne_eq]
  omega

/-- The test `setp.ne … 0` of a non-positive counter. -/
theorem ne_0 {x : Int} (h1 : -2 ^ 32 < x) (h2 : x ≤ 0) :
    scmpi .ne .b (i32 x) 0 = true ↔ x ≠ 0 := by
  simp only [scmpi, PTX.compare, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    decide_eq_true_eq, ne_eq]
  omega

/-- The signed test `setp.lt.s32 … 1` reads the two's complement value. -/
theorem scmpi_lt1 (x : BitVec 64) : scmpi .lt .s x 1 = decide (toSigned 32 (r32 x) < 1) := by
  have h1 : toSigned 32 (i32 1) = 1 := by decide
  simp only [scmpi, PTX.compare, h1]

/-- The negation `sub.s32 … 0, x`. -/
theorem neg_eq (x : BitVec 64) : truncBits 32 (0 - r32 x) = i32 (0 - toSigned 32 (r32 x)) := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r32, i32, truncBits, toSigned, BitVec.toNat_ofNat, BitVec.toNat_sub,
    BitVec.toNat_ofInt]
  split_ifs <;> omega

theorem trunc_toNat (z : BitVec 64) : (truncBits 32 z).toNat = z.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem sub32_toNat (x y : BitVec 64) :
    (sub32 x y).toNat = (x.toNat % 2 ^ 32 + 2 ^ 32 - y.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [sub32, r32, trunc_toNat, BitVec.toNat_sub]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  generalize x.toNat % 2 ^ 32 = a at *
  generalize y.toNat % 2 ^ 32 = b at *
  omega

theorem i32_toNat (z : Int) : (i32 z).toNat = (z % 2 ^ 32).toNat := by
  simp only [i32, trunc_toNat, BitVec.toNat_ofInt]
  omega

theorem addm1_toNat (x : BitVec 64) :
    (addi x (-1)).toNat = (x.toNat % 2 ^ 32 + (2 ^ 32 - 1)) % 2 ^ 32 := by
  have hi : (i32 (-1)).toNat = 2 ^ 32 - 1 := by rw [i32_toNat]; norm_num
  show (truncBits 32 (r32 x + i32 (-1))).toNat = _
  rw [trunc_toNat, BitVec.toNat_add, r32, trunc_toNat, hi,
    Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]

/-- A difference read back: `y - x = -(x - 1 - y) - 1` on words. -/
theorem sub32_swap (x y : BitVec 64) :
    sub32 y x = i32 (0 - toSigned 32 (r32 (sub32 (addi x (-1)) y)) - 1) := by
  apply BitVec.eq_of_toNat_eq
  have hN : (r32 (sub32 (addi x (-1)) y)).toNat % 2 ^ 32 =
      ((x.toNat % 2 ^ 32 + (2 ^ 32 - 1)) % 2 ^ 32 + 2 ^ 32 - y.toNat % 2 ^ 32) % 2 ^ 32 := by
    rw [r32, trunc_toNat, sub32_toNat, addm1_toNat]
    simp only [Nat.mod_mod]
  rw [i32_toNat, sub32_toNat]
  unfold toSigned
  simp only [hN]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  generalize x.toNat % 2 ^ 32 = a at *
  generalize y.toNat % 2 ^ 32 = b at *
  split_ifs <;> omega

theorem xor_01 : xor32 (i32 0) (i32 1) = i32 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [xor32, r32, i32, truncBits]

theorem xor_11 : xor32 (i32 1) (i32 1) = i32 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [xor32, r32, i32, truncBits]

/-- A parity word flipped by `xor.b32 … 1`. -/
theorem xor_par (j : Nat) :
    xor32 (i32 ((j % 2 : Nat) : Int)) (i32 1) = i32 (((j + 1) % 2 : Nat) : Int) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have : (j + 1) % 2 = 1 := by omega
    rw [h, this]; exact xor_01
  · have : (j + 1) % 2 = 0 := by omega
    rw [h, this]; exact xor_11

end PTX.Flow.Arith32
