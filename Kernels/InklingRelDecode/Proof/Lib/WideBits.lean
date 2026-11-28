-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

/-- The sign extension of a 32-bit word to 64 bits, as a natural number. -/
def sx (n : Nat) := n % 2^32 + n % 2^32 / 2^31 * (2^64 - 2^32)

theorem toSigned32_ofNat (a : Nat) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) =
      if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
      else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32 := by
  simp only [toSigned, truncBits, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod_of_dvd a (by decide)
  have h2 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by
    have := Nat.mod_lt a (show 0 < 2 ^ 32 by decide); omega)
  have h3 : a % 2 ^ 32 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod _ _
  simp only [h1, h2, h3]

theorem toSigned64_ofNat (c : Nat) :
    toSigned 64 (truncBits 64 (BitVec.ofNat 64 c)) =
      if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
      else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64 := by
  simp only [toSigned, truncBits, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 % 2 ^ 64 = c % 2 ^ 64 := Nat.mod_mod _ _
  simp only [h1]

theorem sx_two : sx 2 = 2 := by decide

theorem ofInt_two : BitVec.ofInt 64 2 = BitVec.ofNat 64 2 := rfl

theorem madwide_s32 (a b c : Nat) :
    intBits 64 (intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 b)) +
      intOf IType.s 64 (truncBits 64 (BitVec.ofNat 64 c))) =
      BitVec.ofNat 64 ((sx a * sx b + c) % 2 ^ 64) := by
  simp only [intBits, intOf, ite_true]
  rw [toSigned32_ofNat, toSigned32_ofNat, toSigned64_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have ha : ((sx a : Nat) : Int) % 2 ^ 64 =
      (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
        else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sx
    split_ifs <;> push_cast <;> omega
  have hb : ((sx b : Nat) : Int) % 2 ^ 64 =
      (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
        else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sx
    split_ifs <;> push_cast <;> omega
  have hc : (c : Int) % 2 ^ 64 =
      (if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
        else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64) % 2 ^ 64 := by
    split_ifs <;> omega
  generalize (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
      else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sa at *
  generalize (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
      else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sb at *
  generalize (if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
      else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64) = sc at *
  have h : Int.ModEq (2 ^ 64) (sa * sb + sc) ((sx a : Int) * (sx b : Int) + (c : Int)) :=
    Int.ModEq.add (Int.ModEq.mul ha.symm hb.symm) hc.symm
  have h' : (sa * sb + sc) % ((2 ^ 64 : Nat) : Int) =
      (((sx a * sx b + c) % 2 ^ 64 : Nat) : Int) := by
    push_cast
    exact h
  rw [h', Int.toNat_natCast]
  simp

theorem sx_small {b : Nat} (hb : b < 2 ^ 31) : sx b = b := by
  have h1 : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
  have h2 : b / 2 ^ 31 = 0 := by omega
  unfold sx
  rw [h1, h2]
  simp

theorem sx_big {b : Nat} (hb : 2 ^ 31 ≤ b) (hb' : b < 2 ^ 32) : sx b = b + (2 ^ 64 - 2 ^ 32) := by
  have h1 : b % 2 ^ 32 = b := Nat.mod_eq_of_lt hb'
  have h2 : b / 2 ^ 31 = 1 := by omega
  unfold sx
  rw [h1, h2]
  simp

end PTX.Kernels.InklingRelDecode.Proof.Lib
