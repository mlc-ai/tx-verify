-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorSwizzle

@[expose] public section

/-! # The 128-byte swizzle of a tile

The swizzled offset moves with the tile by whole 1024-byte units (eight 128-byte rows keep the
XOR mask), and on a fixed tile it is one to one. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- **Shifting a tile by `1024 t` bytes shifts the offset by `1024 t`**. -/
theorem b128_shift (base v t : Nat) :
    TensorSwizzle.offset .b128 base (v + 1024 * t) =
      TensorSwizzle.offset .b128 (base + 1024 * t) v + 1024 * t := by
  have e1 : BitVec.ofNat 3 ((v + 1024 * t) / 16) = BitVec.ofNat 3 (v / 16) :=
    BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
  have e2 : BitVec.ofNat 3 ((base / 128 + (v + 1024 * t) / 128) % 8) =
      BitVec.ofNat 3 (((base + 1024 * t) / 128 + v / 128) % 8) :=
    BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, e1, e2]
  omega

/-- **The offset of a fixed tile is one to one.** -/
theorem b128_inj (base : Nat) {v w : Nat}
    (h : TensorSwizzle.offset .b128 base v = TensorSwizzle.offset .b128 base w) : v = w := by
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors] at h
  have bv := BitVec.isLt (BitVec.ofNat 3 (v / 16) ^^^ BitVec.ofNat 3 ((base / 128 + v / 128) % 8))
  have bw := BitVec.isLt (BitVec.ofNat 3 (w / 16) ^^^ BitVec.ofNat 3 ((base / 128 + w / 128) % 8))
  have q : v / 128 = w / 128 := by omega
  rw [← q] at h
  have c : (BitVec.ofNat 3 (v / 16) ^^^ BitVec.ofNat 3 ((base / 128 + v / 128) % 8)) =
      (BitVec.ofNat 3 (w / 16) ^^^ BitVec.ofNat 3 ((base / 128 + v / 128) % 8)) :=
    BitVec.eq_of_toNat_eq (by omega)
  have c2 : BitVec.ofNat 3 (v / 16) = BitVec.ofNat 3 (w / 16) := by
    simpa [BitVec.xor_assoc] using congrArg (· ^^^ BitVec.ofNat 3 ((base / 128 + v / 128) % 8)) c
  have c3 := congrArg BitVec.toNat c2
  simp only [BitVec.toNat_ofNat] at c3
  omega

/-- **The offset stays in the 128-byte row of its byte.** -/
theorem b128_range (base v : Nat) :
    128 * (v / 128) ≤ TensorSwizzle.offset .b128 base v ∧
      TensorSwizzle.offset .b128 base v < 128 * (v / 128) + 128 := by
  have b := BitVec.isLt (BitVec.ofNat 3 (v / 16) ^^^
    BitVec.ofNat 3 ((base / 128 + v / 128) % 8))
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors]
  omega
