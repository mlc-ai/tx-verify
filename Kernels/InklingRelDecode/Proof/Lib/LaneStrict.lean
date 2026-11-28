-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.LaneField

@[expose] public section

/-! # The word arithmetic of the exact pieces of the lane-field address

The evaluator's forms of the mask and of the sum of two small words, as the words the control table
holds. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof Arith32

theorem mask_bits (n : Nat) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (n * 2 ^ 21 % 2 ^ 32)) &&&
      truncBits 32 (BitVec.ofInt 64 6291456)) = b32 (n % 4 * 2 ^ 21) := by
  change _ = Value.bits 32 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  have h := and_lane n
  have h1 : (BitVec.ofInt 64 6291456).toNat = 6291456 := by decide
  simp only [truncBits, BitVec.toNat_and, BitVec.toNat_ofNat, h1]
  have e1 : n * 2 ^ 21 % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 = n * 2097152 % 4294967296 := by
    omega
  have e2 : 6291456 % 2 ^ 32 % 2 ^ 64 = 6291456 := by norm_num
  have hb : (n * 2097152 % 4294967296 &&& 6291456) ≤ 6291456 := Nat.and_le_right
  rw [e1, e2]
  omega

theorem sum_bits (a b : Nat) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) +
      truncBits 32 (BitVec.ofNat 64 b)))
      = b32 ((a + b) % 2 ^ 32) := by
  change _ = Value.bits 32 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
