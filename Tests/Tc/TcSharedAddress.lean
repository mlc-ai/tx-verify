-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcSharedAddress

namespace PTX.Tests.TcSharedAddress
open TcShared

private def k128 : Descriptor := ⟨1024, 0, 1024, 0, false, false, .b128⟩
example : byteAddress 2 .k k128 0 0 0 = some 1024 := rfl
example : byteAddress 2 .k k128 1 0 0 = some 1168 := rfl
example : byteAddress 2 .k k128 1 0 1 = some 1169 := rfl
example : byteAddress 2 .k { k128 with start := 1056 } 1 0 0 = some 1200 := rfl
example : byteAddress 2 .k { k128 with start := 128 } 0 0 0 = some 144 := rfl
-- K-major swizzled addressing ignores the leading field.
example : byteAddress 2 .k { k128 with leading := 4096 } 1 0 0 = some 1168 := rfl

-- Canonical examples in ISA §9.7.18.3.3, converted from 16-bit elements to bytes.
private def mnNone : Descriptor := ⟨0, 256, 128, 0, false, false, .none⟩
example : byteAddress 2 .mn mnNone 8 0 0 = some 128 := rfl
example : byteAddress 2 .mn mnNone 0 8 0 = some 256 := rfl
private def mn32 : Descriptor := ⟨0, 256, 512, 0, false, false, .b32⟩
example : byteAddress 2 .mn mn32 8 0 0 = some 16 := rfl
example : byteAddress 2 .mn mn32 16 0 0 = some 256 := rfl
example : byteAddress 2 .mn mn32 0 4 0 = some 144 := rfl
private def k32 : Descriptor := ⟨0, 16, 256, 0, false, false, .b32⟩
example : byteAddress 2 .k k32 1 0 0 = some 32 := rfl
example : byteAddress 2 .k k32 4 0 0 = some 144 := rfl
example : byteAddress 2 .k k32 0 8 0 = some 16 := rfl

-- Unimplemented modes and an out-of-element byte cannot silently alias an address.
example : byteAddress 2 .k { k128 with baseOffset := 1 } 0 0 0 = none := rfl
example : byteAddress 2 .k { k128 with leadingAbsolute := true } 0 0 0 = none := rfl
example : byteAddress 2 .k { k128 with lutSecondSegment := true } 0 0 0 = none := rfl
example : byteAddress 2 .k { k128 with swizzle := .b128x32 } 0 0 0 = none := rfl
example : byteAddress 2 .k k128 0 0 2 = none := rfl

-- The correspondence also covers nonzero TMA swizzle phases and descriptor stepping.
example (base firstK row k byte : Nat) (hb : base % 128 = 0) (hbyte : byte < 2) :
    byteAddress 2 .k ⟨base + 2 * firstK, 0, 1024, 0, false, false, .b128⟩ row k byte =
      some (base + TensorSwizzle.offset .b128 base (128 * row + 2 * (firstK + k) + byte)) :=
  k128_tma_byte 2 base firstK 0 row k byte hb hbyte

-- The same holds for one-byte elements: a 128-byte TMA row holds 128 i8 elements, and
-- the K-th MMA step of 32 elements starts 32 bytes further in the same swizzled row.
example (base firstK row k : Nat) (hb : base % 128 = 0) :
    byteAddress 1 .k ⟨base + firstK, 0, 1024, 0, false, false, .b128⟩ row k 0 =
      some (base + TensorSwizzle.offset .b128 base (128 * row + (firstK + k))) := by
  simpa using k128_tma_byte 1 base firstK 0 row k 0 hb (by decide)
-- Concretely, i8 row 1 of a 128-byte-swizzled tile at a 1024-aligned base: the first
-- 16 bytes land in the second 16-byte chunk and vice versa.
private def k128b : Descriptor := ⟨1024, 0, 1024, 0, false, false, .b128⟩
example : byteAddress 1 .k k128b 1 0 0 = some (1024 + 144) := rfl
example : byteAddress 1 .k k128b 1 16 0 = some (1024 + 128) := rfl
example : byteAddress 1 .k k128b 0 31 0 = some (1024 + 31) := rfl
example : byteAddress 1 .k { k128b with start := 1024 + 32 } 1 0 0 = some (1024 + 176) := rfl
example : byteAddress 1 .k k128b 0 0 1 = none := rfl

-- One-byte elements: sixteen per core-matrix row, then the leading stride.
private def k8 : Descriptor := ⟨4096, 128, 256, 0, false, false, .none⟩
example : byteAddress 1 .k k8 0 15 0 = some 4111 := rfl
example : byteAddress 1 .k k8 0 16 0 = some (4096 + 128) := rfl
example : byteAddress 1 .k k8 7 0 0 = some (4096 + 112) := rfl
example : byteAddress 1 .k k8 8 0 0 = some (4096 + 256) := rfl
-- A one-byte element has no second byte.
example : byteAddress 1 .k k8 0 0 1 = none := rfl
-- Two-byte elements of the same descriptor use eight elements per row.
example : byteAddress 2 .k k8 0 8 0 = some (4096 + 128) := rfl

-- 128B swizzling with 32B atomicity: M/N-major with 4-byte elements (Table 65, Table 67 atom
-- of 8 x 4 sixteen-byte units), 32-byte chunks XORed with the 128-byte row modulo 4.
private def t32 : Descriptor := ⟨0, 4096, 512, 0, false, false, .b128x32⟩
example : byteAddress 4 .mn t32 0 0 0 = some 0 := rfl
example : byteAddress 4 .mn t32 1 0 3 = some 7 := rfl
example : byteAddress 4 .mn t32 8 0 0 = some 32 := rfl
example : byteAddress 4 .mn t32 0 1 0 = some 160 := rfl
example : byteAddress 4 .mn t32 8 1 0 = some 128 := rfl
example : byteAddress 4 .mn t32 0 3 0 = some 480 := rfl
example : byteAddress 4 .mn t32 0 4 0 = some 512 := rfl
example : byteAddress 4 .mn t32 32 0 0 = some 4096 := rfl
-- The swizzle acts on the absolute address: a 128-byte start shifts the row phase.
example : byteAddress 4 .mn { t32 with start := 128 } 0 0 0 = some 160 := rfl
-- K-major has no such atom; the mode is not valid for 1- and 2-byte elements.
example : byteAddress 4 .k t32 0 0 0 = none := rfl
example : byteAddress 1 .mn t32 0 0 0 = none := rfl
example : byteAddress 2 .mn t32 0 0 0 = none := rfl
-- 4-byte M/N-major elements require it.
example : byteAddress 4 .mn { t32 with swizzle := .b128 } 0 0 0 = none := rfl
example : byteAddress 4 .mn { t32 with swizzle := .b64 } 0 0 0 = none := rfl
example : byteAddress 4 .mn { t32 with swizzle := .b32 } 0 0 0 = none := rfl
example : byteAddress 4 .mn { t32 with swizzle := .none } 0 0 0 = none := rfl

end PTX.Tests.TcSharedAddress
