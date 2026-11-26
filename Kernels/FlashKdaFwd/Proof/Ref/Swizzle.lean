-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorSwizzle

/-!
# The 32-byte swizzle: the kernel's address arithmetic against the model's tensor copy

A tensor load with the 32-byte swizzle (the sixteen loads of the FP32 state, tensor map 8)
writes logical byte `byte` of its tile at the address `base + TensorSwizzle.offset .b32 base byte`
(`Core/Async/Tensor/TensorTile.lean: sharedByte`): within every 128-byte row the 16-byte chunks
are exchanged in pairs when the row number plus the 128-byte phase of the tile's base is odd.

The kernel's generic reads and writes of the same buffer (the conversion loop, the carry loads,
the final stores) compute the address of logical byte `byte` as an absolute address `a` and then
flip its bit 4 when its bit 7 is set: `a ^^^ ((a >>> 3) &&& 16)`.

This file proves that the two agree for a tile whose base address is a multiple of 128
(`swzAbs_base`), whatever the parity of `base / 128`: the precondition `sharedBase % 128 = 0`
is enough. It names no thread machine, so every layer can use it.
-/

@[expose] public section

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref

/-- **The kernel's swizzle of an absolute shared address**: bit 4 is flipped when bit 7 is
set. -/
def swzAbs (a : Nat) : Nat := a ^^^ ((a >>> 3) &&& 16)

/-- The swizzle without bit operations. -/
theorem swzAbs_eq_ite (a : Nat) :
    swzAbs a = if a / 128 % 2 = 1 then (if a / 16 % 2 = 0 then a + 16 else a - 16) else a := by
  have hm : (a >>> 3) &&& 16 = if a / 128 % 2 = 1 then 16 else 0 := by
    have h1 : ((a >>> 3) &&& 16) / 2 ^ 4 = (a >>> 3) / 2 ^ 4 &&& 16 / 2 ^ 4 :=
      Nat.and_div_two_pow
    have h2 : ((a >>> 3) &&& 16) % 2 ^ 4 = (a >>> 3) % 2 ^ 4 &&& 16 % 2 ^ 4 :=
      Nat.and_mod_two_pow
    have e1 : (16 : Nat) / 2 ^ 4 = 1 := by decide
    have e2 : (16 : Nat) % 2 ^ 4 = 0 := by decide
    rw [e1, Nat.and_one_is_mod] at h1
    rw [e2, Nat.and_zero] at h2
    rw [Nat.shiftRight_eq_div_pow] at h1 h2 ⊢
    split <;> omega
  have hlow : ∀ r < 32, r ^^^ 16 = if r / 16 % 2 = 0 then r + 16 else r - 16 := by decide
  have h1 : (a ^^^ 16) / 2 ^ 5 = a / 2 ^ 5 ^^^ 16 / 2 ^ 5 := Nat.xor_div_two_pow
  have h2 : (a ^^^ 16) % 2 ^ 5 = a % 2 ^ 5 ^^^ 16 % 2 ^ 5 := Nat.xor_mod_two_pow
  have e1 : (16 : Nat) / 2 ^ 5 = 0 := by decide
  have e2 : (16 : Nat) % 2 ^ 5 = 16 := by decide
  have e3 : (2 : Nat) ^ 5 = 32 := by decide
  rw [e1, Nat.xor_zero] at h1
  rw [e2, e3, hlow (a % 32) (Nat.mod_lt _ (by decide))] at h2
  rw [e3] at h1
  unfold swzAbs
  rw [hm]
  split
  · split at h2 <;> split <;> omega
  · exact Nat.xor_zero a

/-- The kernel's swizzle is the model's 32-byte swizzle of a tile at address 0. -/
theorem swzAbs_offset (a : Nat) : swzAbs a = TensorSwizzle.offset .b32 0 a := by
  have hx : ∀ c : BitVec 3, (c ^^^ 1#3).toNat =
      if c.toNat % 2 = 0 then c.toNat + 1 else c.toNat - 1 := by decide
  rw [swzAbs_eq_ite]
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, Nat.zero_div, Nat.zero_add]
  by_cases h : a / 128 % 2 = 1
  · simp only [h, ite_true]
    rw [hx]
    simp only [BitVec.toNat_ofNat]
    split <;> split <;> omega
  · have h0 : a / 128 % 2 = 0 := by omega
    simp only [h0, Nat.zero_ne_one, ite_false]
    change _ = 128 * (a / 128) + 16 * ((BitVec.ofNat 3 (a / 16)) ^^^ 0#3).toNat + a % 16
    rw [BitVec.xor_zero]
    simp only [BitVec.toNat_ofNat]
    omega

/-- **The kernel's address of a logical byte is the model's**: for a tile at a base address
that is a multiple of 128, swizzling the absolute address `base + byte` gives the address at
which a tensor copy with the 32-byte swizzle keeps logical byte `byte` of the tile. -/
theorem swzAbs_base (base byte : Nat) (hb : base % 128 = 0) :
    swzAbs (base + byte) = base + TensorSwizzle.offset .b32 base byte := by
  rw [swzAbs_offset, TensorSwizzle.offset_add_base _ _ _ hb]

/-- The swizzle is its own inverse. -/
theorem swzAbs_swzAbs (a : Nat) : swzAbs (swzAbs a) = a := by
  rw [swzAbs_offset, swzAbs_offset, TensorSwizzle.offset_involutive]

/-- The swizzle keeps the 128-byte row and the position within the 16-byte chunk. -/
theorem swzAbs_row (a : Nat) : swzAbs a / 128 = a / 128 ∧ swzAbs a % 16 = a % 16 := by
  rw [swzAbs_offset]
  exact ⟨TensorSwizzle.offset_row _ _ _, TensorSwizzle.offset_byte _ _ _⟩

end PTX.Kernels.FlashKdaFwd.Proof.Ref
