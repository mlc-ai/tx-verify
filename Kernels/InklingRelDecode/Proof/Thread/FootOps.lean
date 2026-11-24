-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeProCopy

@[expose] public section

/-! # The 32-bit exclusive-or and inclusive-or on numbers

`ProBOps` has the integer operations of the code's register table on operands `BitVec.ofNat 64 a`
as `BitVec.ofNat 64 e`; it lacks the bitwise exclusive-or and inclusive-or, which the swizzled
shared addresses of the query tile (`FootQ`) use. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem wXor32_ofNat (a b : Nat) :
    wXor32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 ((a % 2 ^ 32) ^^^ (b % 2 ^ 32)) := by
  simp only [wXor32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have h2 : b % 2 ^ 32 % 2 ^ 64 = b % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have h3 : (a % 2 ^ 32) ^^^ (b % 2 ^ 32) < 2 ^ 32 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  rw [h1, h2, Nat.mod_eq_of_lt (by omega : (a % 2 ^ 32) ^^^ (b % 2 ^ 32) < 2 ^ 64)]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
