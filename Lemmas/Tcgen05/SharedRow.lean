-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcSharedAddress
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The 128-byte row of a shared operand byte

A proof tool for operand footprints: the shared address of an operand byte
(`TcShared.byteAddress`) in the 128-byte swizzled mode lies in the 128-byte row of the unswizzled
address (`byteAddress_b128_row`); without swizzling it is the unswizzled address
(`byteAddress_none_eq`). -/

namespace PTX.TcShared

/-- **A 128-byte-swizzled operand byte keeps its 128-byte row.** -/
theorem byteAddress_b128_row {w : Nat} {major : Major} {d : Descriptor} {row k byte a : Nat}
    (hs : d.swizzle = .b128) (h : byteAddress w major d row k byte = some a) :
    a / 128 = (d.start + linear w major .b128 d row k + byte) / 128 := by
  unfold byteAddress at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [hs]
    simp only [Swizzle.offset]
    rw [TensorSwizzle.offset_row]
  · cases h

/-- **An unswizzled operand byte is at its linear address.** -/
theorem byteAddress_none_eq {w : Nat} {major : Major} {d : Descriptor} {row k byte a : Nat}
    (hs : d.swizzle = .none) (h : byteAddress w major d row k byte = some a) :
    a = d.start + linear w major .none d row k + byte := by
  unfold byteAddress at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rw [hs]
    simp only [Swizzle.offset, TensorSwizzle.offset_none]
  · cases h

end PTX.TcShared
