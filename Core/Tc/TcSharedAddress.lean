-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcSharedDescriptor

@[expose] public section

namespace PTX.TcShared

/-! ## THREAD-TC-SHARED-ADDRESS — canonical operand byte addresses
Statement: Element (row, k) of an MMA operand in shared memory lies at the offset that the canonical
  K-major or MN-major layout gives with the descriptor's strides and core matrices of 8 rows of 16
  bytes, added to the start address and passed through the absolute-address XOR swizzle of the mode.
  No address exists for an absolute leading offset, the LUT mode, a nonzero base offset, the
  32-byte-atomic 128-byte mode with a K-major operand or with MN-major 1- or 2-byte elements, or
  MN-major 4-byte elements in any other mode. A core-matrix row holds `16 / width` elements. K-major
  swizzled layouts ignore the leading stride, as the text specifies, and MN-major layouts use both
  strides. The 128-byte mode with 32-byte atomicity has swizzle atoms of 8 16-byte units along M or
  N by 4 along K, applies to MN-major layouts only, and is required exactly for 4-byte elements (the
  transposed kind::tf32 of Table 65).

Defs: TcShared.Major, TcShared.linear, TcShared.byteAddress

Source:
- §9.7.18.3.3 (canonical layouts: core matrices of 8 rows by 16 bytes, T = 16 / element bytes)
- §9.7.18.10.6 Table 67 (Layout for swizzle atoms, 128b element: the row for 128B swizzling with 32B
    atomicity gives 8x4 for M/N-major and no K-major atom; the row for 128B swizzling with 16B
    atomicity gives 8x8 for M/N-major and 8x8 for K-major)
- §9.7.18.10.3 Table 65 (for 32-bit elements, a transposed A or B is supported only with 128B
    swizzling with 32B atomicity; for 8-bit and 16-bit elements, a transposed A or B takes every
    swizzling mode except that one)
- §5.5.7 32-byte-atomicity pattern (THREAD-TENSOR-SWIZZLE); NVIDIA CUTLASS
    include/cute/arch/mma_sm100_desc.hpp make_umma_desc (Swizzle composed after shared pointer and
    layout; LayoutType::B128_BASE32B: Swizzle<2,5,2> o smem_ptr o ((8,n),(4,k)):((1,LBO),(8,SBO)),
    commented there as not applicable for Major-K)

Direction: scope

Applies: 1-byte (kind::i8), 2-byte (kind::f16) and 4-byte (kind::tf32) elements in relative-leading
  canonical K-major or MN-major layouts, base-offset field zero; the 32-byte-atomic 128-byte mode
  only MN-major and only with 4-byte elements

Premises: Descriptor decoding and instruction shape checks are separate. The byte is within one
  element; absolute leading, LUT and shifted-pattern modes are not handled by this component.

Effect: Address calculation only. Unsupported modes return none, with no guessed address: K-major
  with the 32-byte-atomic mode, MN-major 4-byte elements with any other mode, and MN-major 1- and
  2-byte elements with the 32-byte-atomic mode.

Review: The raw descriptor decoder keeps nonzero base offsets. `byteAddress` accepts only base
  offset zero, and the shifted-pattern rule is not modeled. The TMA swizzle primitive is reused with
  base zero on the absolute byte address.
-/
/-- The major order of an operand in shared memory: K-major, where the contraction dimension is
contiguous, or MN-major, where the M or N dimension is contiguous (a transposed operand). -/
inductive Major where
  | k | mn
  deriving DecidableEq, Repr

/-- Row is the non-contracting coordinate, k is the contracting coordinate.
Both A and B use this convention; the B operand is indexed as (N,K). -/
def linear (width : Nat) (major : Major) (s : Swizzle) (d : Descriptor)
    (row k : Nat) : Nat :=
  let sectors := s.sectors
  let atom := 16 / width
  let kAtom := if s = .b128x32 then 4 else 8
  match major with
  | .k =>
    16 * sectors * (row % 8) + d.stride * (row / 8) +
      if s = .none then width * (k % atom) + d.leading * (k / atom) else width * k
  | .mn =>
    if s = .none then
      width * (row % atom) + d.stride * (row / atom) + 16 * (k % 8) + d.leading * (k / 8)
    else
      width * (row % atom) + 16 * (row / atom % sectors) + d.leading * (row / (atom * sectors)) +
        16 * sectors * (k % kAtom) + d.stride * (k / kAtom)

/-- The shared-memory byte address of byte `byte` of element (`row`, `k`) of an operand with
`width`-byte elements in the canonical layout of `major` that `d` describes, after the swizzle of
its mode; `none` for the modes this component does not handle. -/
def byteAddress (width : Nat) (major : Major) (d : Descriptor) (row k byte : Nat) : Option Nat :=
  if d.leadingAbsolute = false ∧ d.lutSecondSegment = false ∧ d.baseOffset = 0 ∧ byte < width ∧
      (major = .k → d.swizzle ≠ .b128x32) ∧ (major = .mn → (d.swizzle = .b128x32 ↔ width = 4)) then
    some (d.swizzle.offset (d.start + linear width major d.swizzle d row k + byte))
  else none

end PTX.TcShared
