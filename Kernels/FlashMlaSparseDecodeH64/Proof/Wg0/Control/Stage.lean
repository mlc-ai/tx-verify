-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
public import Lemmas.Flow.Swizzle

@[expose] public section

/-! # The staging pointers' bytes: bounds and the swizzle's normal form

The row's offset is below `2 ^ 15` (`stQuad_lt`), each chunk's unswizzled byte and the pointer's
swizzled byte are below `2 ^ 32` (`stP_lt`, `stW_lt`); the widened base word is the base
(`zext_sbw`); the swizzle's xor as the evaluation writes it (`stage_xor`, `st_norm`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
open PTX PTX.Flow PTX.Proof PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The row's byte offset is below `2 ^ 15`. -/
theorem stQuad_lt (L : Launch) (g : Nat) : (stQuad L g).toNat < 2 ^ 15 := by
  have htr : ∀ y : BitVec 64, (truncBits 32 y).toNat ≤ y.toNat := fun y => by
    simp only [truncBits, BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.mod_le _ _)
  have hand : ∀ a b : BitVec 64, (a &&& b).toNat ≤ b.toNat := fun a b => by
    rw [BitVec.toNat_and]; exact Nat.and_le_right
  have ha : (r32 (andi (shl (tw L g) 6) 4032)).toNat < 2 ^ 14 :=
    Nat.lt_of_le_of_lt (htr _) (Nat.lt_of_le_of_lt (hand _ _) (by decide))
  have hb : (r32 (andi (shl (tw L g) 7) 8192)).toNat < 2 ^ 14 :=
    Nat.lt_of_le_of_lt (htr _) (Nat.lt_of_le_of_lt (hand _ _) (by decide))
  have hr : (r32 (stRow L g)).toNat < 2 ^ 14 := by
    refine Nat.lt_of_le_of_lt (htr _) ?_
    show (r32 (andi (shl (tw L g) 6) 4032) ||| r32 (andi (shl (tw L g) 7) 8192)).toNat < 2 ^ 14
    rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow ha hb
  show (BitVec.ofNat 64 ((r32 (stRow L g)).toNat * (i32 2).toNat)).toNat < 2 ^ 15
  have h2 : (i32 2).toNat = 2 := by decide
  rw [BitVec.toNat_ofNat, h2]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

/-- The unswizzled bytes are below `2 ^ 32`. -/
theorem stP_lt (hp : Pre P L m) (g : Nat) {k : Nat} (hk : k < 8) : stP L g k < 2 ^ 32 := by
  have := sharedBase_lt hp
  have := stQuad_lt L g
  unfold stP; omega

/-- The shared base word, widened, is the base's number. -/
theorem zext_sbw (hp : Pre P L m) : zext (sbw L) = BitVec.ofNat 64 L.sharedBase := by
  have := sharedBase_lt hp
  apply BitVec.eq_of_toNat_eq
  simp only [zext, sbw, r32, truncBits, BitVec.toNat_ofNat, Nat.add_zero]
  omega

/-- The swizzle's xor of a pointer below `2 ^ 32` with its masked eighth. -/
theorem stage_xor {A : Nat} (hA : A < 2 ^ 32) :
    BitVec.ofNat 64 ((A / 8 % 18446744073709551616 &&& 112) % 18446744073709551616) ^^^
      BitVec.ofNat 64 A = BitVec.ofNat 64 ((A / 8 &&& 112) ^^^ A) := by
  have h2 : A / 8 % 18446744073709551616 = A / 8 := Nat.mod_eq_of_lt (by omega)
  have h3 : (A / 8 &&& 112) % 18446744073709551616 = A / 8 &&& 112 :=
    Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (n := 64) (by decide))
  rw [h2, h3, nf_xor]
  rw [show A % 18446744073709551616 = A from Nat.mod_eq_of_lt (by omega), h3]

/-- The pointer's bits as the swizzle's shift reads them. -/
theorem st_norm {A : Nat} (hA : A < 2 ^ 32) :
    (Int.ofNat (A % 18446744073709551616) % 18446744073709551616).toNat % 18446744073709551616
      = A := by
  have h : A % 18446744073709551616 = A := Nat.mod_eq_of_lt (by omega)
  rw [h, Int.ofNat_eq_natCast, Int.emod_eq_of_lt (Int.natCast_nonneg A) (by omega),
    Int.toNat_natCast, h]

/-- The swizzled bytes are below `2 ^ 32`. -/
theorem stW_lt (hp : Pre P L m) (g : Nat) {k : Nat} (hk : k < 8) : stW L g k < 2 ^ 32 := by
  have h1 := stP_lt hp g hk
  have h2 : stM L g k < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  exact Nat.xor_lt_two_pow h2 h1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control
