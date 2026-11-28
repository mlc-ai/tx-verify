-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof Arith32

/-- The multiply-high quotient at the head of the loop agrees with natural division
on each in-bounds block number. -/
theorem quotient_eq {i : BitVec 64} (hi : i.toNat < 2 ^ 31) :
    quotient i = BitVec.ofNat 64 (i.toNat / 3) := by
  have ri : r32 i = i := by
    apply BitVec.eq_of_toNat_eq
    simp only [r32, truncBits, BitVec.toNat_ofNat]
    omega
  have si : toSigned 32 i = (i.toNat : Int) := by
    simp only [toSigned]
    split <;> omega
  have q : (i.toNat : Int) * 1431655766 / 2 ^ 32 = (i.toNat / 3 : Nat) := by omega
  unfold quotient
  rw [ri, si, q]
  let y := BitVec.ofNat 64 (i.toNat / 3)
  have yN : y.toNat = i.toNat / 3 := Nat.mod_eq_of_lt (by omega)
  have ry : r32 y = y := by
    apply BitVec.eq_of_toNat_eq
    rw [show (r32 y).toNat = (y.toNat % 2 ^ 32) % 2 ^ 64 by rfl, yN]
    clear ri si q
    omega
  change add32 (r32 y) (shru (r32 y) 31) = y
  rw [ry]
  have hy : shru y 31 = 0 := by
    change (if (i32 31).toNat ≥ 32 then 0 else r32 y >>> (i32 31).toNat) = 0
    rw [ite_eq_right_of_eq_false _ _ (by decide), show (i32 31).toNat = 31 by rfl, ry]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, yN, Nat.shiftRight_eq_div_pow]
    change i.toNat / 3 / 2 ^ 31 = 0
    omega
  rw [hy]
  change r32 (r32 y + r32 0) = y
  rw [ry, show r32 0 = 0 by rfl, add_zero, ry]

end PTX.Kernels.InklingRelDecode.Proof.Loader
