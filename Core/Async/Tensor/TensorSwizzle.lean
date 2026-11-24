-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.BitVec

@[expose] public section

namespace PTX.TensorSwizzle

/-! ## THREAD-TENSOR-SWIZZLE — 16-byte-atom tensor shared-memory swizzles
Statement: A swizzle permutes the 16-byte chunks within each 128-byte row of a shared tile by
  XOR with a value that depends on the row number and on the 128-byte phase of the base address.
  Bytes within a chunk keep their order. The 128-byte swizzle with 32-byte atomicity permutes the
  four 32-byte chunks of a row in the same way.

Defs: TensorSwizzle.Mode, TensorSwizzle.sectors, TensorSwizzle.mask, TensorSwizzle.chunk,
  TensorSwizzle.offset, TensorSwizzle.offset128x32

Source:
- §5.5.7 (128 byte swizzle mode, 32-byte atomicity sub-mode): "In this sub-mode, the 32-byte of data
    is kept intact while swizzling. The following table where each element (numbered cell) is 16
    byte shows the swizzling pattern at the destination data layout: 0 1 2 3 4 5 6 7 2 3 0 1 6 7 4 5
    4 5 6 7 0 1 2 3 6 7 4 5 2 3 0 1 … Pattern repeats …"
- CUDA Programming Guide §4.13.2, Table 27

Direction: reading

Applies: No swizzle and 32/64/128-byte swizzles with 16-byte atoms (`offset`); the 128-byte swizzle
  with 32-byte atoms (`offset128x32`)

Premises: The consuming tensor operation validates shared base alignment and tile layout. The input
  offset is in the padded, unswizzled shared layout.

Effect: Address computation only. A pattern row is 128 physical bytes, which need not be a tensor
  row. `offset128x32` is the 32-byte-atomicity sub-mode: the four 32-byte chunks of a 128-byte row
  are permuted by XOR with the row number modulo 4 (the table's rows 0, 2 3 0 1 6 7 4 5, ... are the
  16-byte indices `i ^ 2r`), keeping 32 bytes intact; it is not a `Mode` because the TMA descriptor
  does not use it here. The 8-byte-flip sub-mode and 64-byte atomicity are not represented. Tile
  padding is a separate layout operation.
-/
/-- The swizzle mode of a shared tile: no swizzle, or the 32, 64 or 128 byte swizzle. -/
inductive Mode where
  | none | b32 | b64 | b128
  deriving DecidableEq, Repr

/-- The number of distinct XOR values of a mode: 1, 2, 4 and 8. -/
def sectors : Mode → Nat
  | .none => 1
  | .b32 => 2
  | .b64 => 4
  | .b128 => 8

/-- The XOR value for 128-byte row `row` of a tile at address `base`: the sum of the row number and
the 128-byte phase of the base, modulo the number of distinct values of the mode. -/
def mask (mode : Mode) (base row : Nat) : BitVec 3 :=
  BitVec.ofNat 3 ((base / 128 + row) % sectors mode)

/-- The physical 16-byte chunk of the row that holds logical chunk `col`: `col` XOR the mask. -/
def chunk (mode : Mode) (base row : Nat) (col : BitVec 3) : BitVec 3 :=
  col ^^^ mask mode base row

/-- The swizzled byte offset of the unswizzled byte offset `byte` of a tile at address `base`: its
16-byte chunk is permuted within its 128-byte row and its position within the chunk is kept. -/
def offset (mode : Mode) (base byte : Nat) : Nat :=
  128 * (byte / 128) +
    16 * (chunk mode base (byte / 128) (BitVec.ofNat 3 (byte / 16))).toNat + byte % 16

/-- 128-byte swizzle with 32-byte atomicity: the 32-byte chunk index (0..3) of a physical
128-byte row is XORed with `(base / 128 + row) % 4`. -/
def offset128x32 (base byte : Nat) : Nat :=
  128 * (byte / 128) + 32 * (byte / 32 % 4 ^^^ (base / 128 + byte / 128) % 4) + byte % 32

end PTX.TensorSwizzle
