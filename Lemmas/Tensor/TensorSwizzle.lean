-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.TensorSwizzle

theorem chunk_involutive (mode : Mode) (base row : Nat) (col : BitVec 3) :
    chunk mode base row (chunk mode base row col) = col := by
  simp [chunk, BitVec.xor_assoc]

theorem offset_row (mode : Mode) (base byte : Nat) :
    offset mode base byte / 128 = byte / 128 := by
  have h := (chunk mode base (byte / 128) (BitVec.ofNat 3 (byte / 16))).isLt
  simp only [offset]
  omega

theorem offset_byte (mode : Mode) (base byte : Nat) :
    offset mode base byte % 16 = byte % 16 := by
  simp [offset, Nat.add_mod, Nat.mul_mod]

theorem offset_chunk (mode : Mode) (base byte : Nat) :
    BitVec.ofNat 3 (offset mode base byte / 16) =
      chunk mode base (byte / 128) (BitVec.ofNat 3 (byte / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have h := (chunk mode base (byte / 128) (BitVec.ofNat 3 (byte / 16))).isLt
  simp only [BitVec.toNat_ofNat, offset]
  omega

theorem offset_involutive (mode : Mode) (base byte : Nat) :
    offset mode base (offset mode base byte) = byte := by
  change 128 * (offset mode base byte / 128) +
    16 * (chunk mode base (offset mode base byte / 128)
      (BitVec.ofNat 3 (offset mode base byte / 16))).toNat +
    offset mode base byte % 16 = byte
  rw [offset_row, offset_chunk, chunk_involutive, offset_byte]
  simp only [BitVec.toNat_ofNat]
  omega

theorem offset_injective (mode : Mode) (base : Nat) :
    Function.Injective (offset mode base) := by
  intro a b h
  have := congrArg (offset mode base) h
  simpa only [offset_involutive] using this

theorem offset_none (base byte : Nat) : offset .none base byte = byte := by
  simp only [offset, chunk, mask, sectors, Nat.mod_one]
  change 128 * (byte / 128) + 16 *
    ((BitVec.ofNat 3 (byte / 16)) ^^^ (0 : BitVec 3)).toNat + byte % 16 = byte
  change 128 * (byte / 128) + 16 * ((byte / 16) % 8 ^^^ 0) + byte % 16 = byte
  rw [Nat.xor_zero]
  omega

/-- Absolute-address swizzling agrees with TMA's base-relative form when the
shared base is 128-byte aligned. Its phase need not be aligned to a full pattern. -/
theorem offset_add_base (mode : Mode) (base byte : Nat) (hb : base % 128 = 0) :
    offset mode 0 (base + byte) = base + offset mode base byte := by
  have hr : (base + byte) / 128 = base / 128 + byte / 128 := by omega
  have hc : BitVec.ofNat 3 ((base + byte) / 16) = BitVec.ofNat 3 (byte / 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have hl : (base + byte) % 16 = byte % 16 := by omega
  unfold offset
  rw [hr, hc, hl]
  simp only [chunk, mask, Nat.zero_div, Nat.zero_add]
  omega

end PTX.TensorSwizzle
