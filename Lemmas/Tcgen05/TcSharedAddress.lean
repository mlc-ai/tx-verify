-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcSharedAddress
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.TcShared

theorem linear_k128 (w : Nat) (d : Descriptor) (row k : Nat) (hs : d.stride = 1024) :
    linear w .k .b128 d row k = 128 * row + w * k := by
  simp only [linear, Swizzle.sectors, reduceCtorEq, ite_false, hs]
  omega

/-- An MMA descriptor advanced along K selects the same byte as TMA's packed
128-byte row layout, for elements of any width. No fixed tile size, stage count, CTA or
base address is used. -/
theorem k128_tma_byte (w base firstK leading row k byte : Nat)
    (hb : base % 128 = 0) (hbyte : byte < w) :
    byteAddress w .k ⟨base + w * firstK, leading, 1024, 0, false, false, .b128⟩ row k byte =
      some (base + TensorSwizzle.offset .b128 base (128 * row + w * (firstK + k) + byte)) := by
  simp [byteAddress, Swizzle.offset, hbyte]
  rw [linear_k128 w _ row k rfl]
  have he : base + w * firstK + (128 * row + w * k) + byte =
      base + (128 * row + w * (firstK + k) + byte) := by rw [Nat.mul_add]; omega
  rw [he, TensorSwizzle.offset_add_base _ _ _ hb]

/-- One-byte K-major, unswizzled: the canonical layout ((8,m),(16,2k)) of 8-bit elements. -/
theorem byteAddress1_k_none (start leading stride row k : Nat) :
    byteAddress 1 .k ⟨start, leading, stride, 0, false, false, .none⟩ row k 0 =
      some (start + 16 * (row % 8) + stride * (row / 8) + k % 16 + leading * (k / 16)) := by
  simp only [byteAddress, linear, Swizzle.offset, Swizzle.sectors, TensorSwizzle.offset_none]
  simp
  omega

end PTX.TcShared
