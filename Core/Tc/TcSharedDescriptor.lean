-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.TcShared

/-! ## THREAD-TC-SHARED-DESCRIPTOR — shared matrix descriptor fields
Statement: A 64-bit shared matrix descriptor decodes into a start address, a leading and a stride
  byte offset (each encoded in 16-byte units), a base offset, the leading-absolute and LUT flags and
  one of five swizzling modes. The start and leading fields are bits 0–14 and 16–30, and the stride
  field is bits 32–45. A word with a set reserved bit, a version field other than 1 or an
  undocumented swizzle code does not decode, and the instruction that uses it has no rule.

Defs: TcShared.Swizzle, TcShared.decodeSwizzle, TcShared.Swizzle.sectors, TcShared.Swizzle.offset,
  TcShared.Descriptor, TcShared.decode

Source:
- §9.7.18.4.1 Table 49 and Table 50

Direction: reading

Applies: 64-bit tcgen05 shared-memory matrix descriptors

Premises: The word has zero reserved bits, the fixed version field 001, and a documented swizzle
  code.

Effect: Field decoding, and the swizzle of each encoding (`Swizzle.sectors`, `Swizzle.offset`). The
  leading absolute-address flag is kept as a field, so absolute leading mode is never read as a
  relative offset, and the 32-byte-atomic swizzle has its own offset function,
  `TensorSwizzle.offset128x32`, distinct from the 16-byte-atomic one.

Review: Table 49 names 15-bit start/leading fields. Its address-encoding formula masks byte
  addresses with 0x3ffff before shifting. The decoder keeps the table's fields. It does not
  establish that a decoded word is a valid encoded address for a target, and leaves that to the
  shared-memory access and allocation checks.
-/
/-- The swizzling mode of a shared matrix descriptor (Table 50): no swizzling, 128-byte swizzling
with 32-byte atomicity, or 128-byte, 64-byte or 32-byte swizzling. -/
inductive Swizzle where
  | none | b128x32 | b128 | b64 | b32
  deriving DecidableEq, Repr

/-- The swizzling mode of the 3-bit code at bits 61 to 63; the other codes are undocumented. -/
def decodeSwizzle : Nat → Option Swizzle
  | 0 => some .none
  | 1 => some .b128x32
  | 2 => some .b128
  | 4 => some .b64
  | 6 => some .b32
  | _ => none

/-- 16-byte chunks per swizzle-atom row (8 for both 128-byte modes). -/
def Swizzle.sectors : Swizzle → Nat
  | .none => 1
  | .b32 => 2
  | .b64 => 4
  | .b128 | .b128x32 => 8

/-- The absolute-address XOR swizzle of the mode (pattern phase zero). -/
def Swizzle.offset : Swizzle → Nat → Nat
  | .none => TensorSwizzle.offset .none 0
  | .b32 => TensorSwizzle.offset .b32 0
  | .b64 => TensorSwizzle.offset .b64 0
  | .b128 => TensorSwizzle.offset .b128 0
  | .b128x32 => TensorSwizzle.offset128x32 0

/-- A decoded 64-bit shared matrix descriptor (§9.7.18.4.1 Table 49), which locates an MMA or
copy operand in shared memory. The address and offset fields are in bytes. -/
structure Descriptor where
  /-- The matrix start address: bits 0 to 14 times 16. -/
  start : Nat
  /-- The leading dimension byte offset, or the absolute leading address when `leadingAbsolute`
  is set: bits 16 to 30 times 16. -/
  leading : Nat
  /-- The stride dimension byte offset: bits 32 to 45 times 16. -/
  stride : Nat
  /-- The matrix base offset: bits 49 to 51. -/
  baseOffset : Nat
  /-- Bit 52: the leading field holds an absolute address. -/
  leadingAbsolute : Bool
  /-- Bit 53: the lookup-table second-segment flag. -/
  lutSecondSegment : Bool
  /-- The swizzling mode: bits 61 to 63. -/
  swizzle : Swizzle
  deriving DecidableEq, Repr

/-- Decode the 64-bit shared matrix descriptor `x`. A word with a set reserved bit (bit 15, bit
31 or bits 54 to 60), a version field (bits 46 to 48) other than 1, or an undocumented swizzle
code decodes to nothing. -/
def decode (x : Nat) : Option Descriptor :=
  match decodeSwizzle (x / 2 ^ 61 % 8) with
  | none => none
  | some swizzle =>
    if x < 2 ^ 64 ∧ x / 2 ^ 15 % 2 = 0 ∧ x / 2 ^ 31 % 2 = 0 ∧
        x / 2 ^ 46 % 8 = 1 ∧ x / 2 ^ 54 % 128 = 0 then
      some {
        start := x % 2 ^ 15 * 16
        leading := x / 2 ^ 16 % 2 ^ 15 * 16
        stride := x / 2 ^ 32 % 2 ^ 14 * 16
        baseOffset := x / 2 ^ 49 % 8
        leadingAbsolute := x / 2 ^ 52 % 2 = 1
        lutSecondSegment := x / 2 ^ 53 % 2 = 1
        swizzle := swizzle }
    else none

end PTX.TcShared
