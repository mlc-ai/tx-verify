-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Entry

@[expose] public section

/-! # Words that are multiples of 8

The mbarrier words of a role are the shared base plus multiples of 8 (a slot times 8, a slot times
a multiple of 8, a constant offset), formed with 32-bit arithmetic. `M8 x` says the word is a
multiple of 8; it holds for the shared base and is kept by the 32-bit sums, shifts by 3 and
multiply-adds of such words, whatever the slot. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Flow.Arith32

/-- The word is a multiple of 8. -/
def M8 (x : BitVec 64) : Prop := x.toNat % 8 = 0

theorem m8_sbw {P : Params} {L : Launch} {m : Mem0} (hp : Pre P L m) : M8 (sbw L) := by
  have h1 := hp.sharedAlignment
  have h2 := hp.sharedBase
  unfold M8
  simp only [sbw, truncBits, BitVec.toNat_ofNat]
  omega

theorem m8_add32 {x y : BitVec 64} (hx : M8 x) (hy : M8 y) : M8 (add32 x y) := by
  unfold M8 at *
  simp only [add32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  omega

theorem m8_addi {x : BitVec 64} {n : Int} (hx : M8 x) (hn : n % 8 = 0) : M8 (addi x n) := by
  unfold M8 at *
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

theorem m8_shl3 (x : BitVec 64) : M8 (shl x 3) := by
  unfold M8
  simp only [shl, i32, truncBits, r32, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    BitVec.toNat_shiftLeft]
  norm_num
  omega

theorem m8_mad32 {x y z : BitVec 64} (hy : M8 (r32 y)) (hz : M8 z) : M8 (mad32 x y z) := by
  unfold M8 at *
  simp only [mad32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_mul] at *
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hy
  rw [hk, show x.toNat % 2 ^ 32 % 2 ^ 64 * (8 * k) = 8 * (x.toNat % 2 ^ 32 % 2 ^ 64 * k) by ring]
  generalize x.toNat % 2 ^ 32 % 2 ^ 64 * k = w
  omega

theorem m8_i32 {n : Int} (hn : n % 8 = 0) : M8 (r32 (i32 n)) := by
  unfold M8
  simp only [r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
