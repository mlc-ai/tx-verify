-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcSharedAddress
public import Core.Tc.TcMmaResultLayout
public import Core.Sync.Cluster

@[expose] public section

namespace PTX.TcCopy

/-! ## THREAD-TC-CP-CELLS — shared source and Tensor Memory destination of tcgen05.cp
Statement: A `tcgen05.cp` copies, in each CTA of its group, a matrix of `rows` rows of `rowBytes`
  bytes, which a shared matrix descriptor locates in that CTA's shared memory as a K-major matrix of
  one-byte elements, into the Tensor Memory of the same CTA. Source row r lands, byte by byte in
  order, in the words of the address's columns at each lane the shape's multicast assigns to r (with
  decompression, the bytes of THREAD-TC-CP-DECOMPRESS). The address must have lane field 0, and a
  word is known only when the source bytes it depends on are known.

Defs: TcCpShape.rows, TcCpShape.rowBytes, TcCpShape.sourceBytes, TcCpShape.lanes, TcCopy.Spec,
  TcCopy.AddressOk, TcCopy.addressOkDecidable, TcCopy.byteLoc, TcCopy.cell,
  TcCopy.byteValue, TcCopy.word

Source:
- §9.7.18.9.2: "When .cta_group::1 is specified, the data is copied into the Tensor Memory of the
    current CTA."
- §9.7.18.9.2: "A thread executing a tcgen05.cp instruction with .cta_group::2 causes both the
    current and peer CTA to copy data from their shared memory to Tensor Memory ."
- §9.7.18.9.2: "When the .multicast qualifier is specified as either .warpx2::02_13 or
    .warpx2::01_23 then the data being copied is multicasted into warp pairs and each warp in the
    warp pair receive half of the data."
- §9.7.18.9.2: ".warpx2::02_13 : warps 0 and 2 form a pair; warps 1 and 3 form a pair."
- §9.7.18.9.2: ".warpx2::01_23 : warps 0 and 1 form a pair; warps 2 and 3 form a pair."
- §9.7.18.9.2: "When the .multicast modifier is specified as .warpx4 then the data being copied is
    multicasted into all 4 warps."
- §9.7.18.2.3 (data movement shape `lane x size`)
- §9.7.18.8.1 (warp `w` of a warpgroup accesses lanes `32 w` to `32 w + 31`)
- §9.7.18.4.1 (shared matrix descriptor)
- EXT-TCCP

Direction: reading

Applies: tcgen05.cp.cta_group::{1,2} of `.128x256b`, `.4x256b`, `.128x128b`,
  `.64x128b.warpx2::02_13`, `.64x128b.warpx2::01_23` and `.32x128b.warpx4`, with or without
  decompression (THREAD-TC-CP-DECOMPRESS)

Premises: A decoded shared descriptor of the represented canonical modes; a Tensor Memory address
  with lane field 0 and the shape's columns within the 512 physical ones; with `.cta_group::2`, the
  pair's CTAs in the launch.

Effect: Address and value geometry only; issue, completion and ordering are execution rules.
  `.128x256b` copies 128 rows of 32 bytes and `.128x128b` 128 rows of 16 bytes, row `r` to lane `r`.
  `.64x128b` copies 64 rows of 16 bytes: with `.warpx2::02_13` row `r` goes to lanes `r` and
  `r + 64` (the pair of warps 0 and 2 holds rows 0 to 31, the pair of warps 1 and 3 rows 32 to 63),
  and with `.warpx2::01_23` row `r` goes to lanes `r % 32 + 64 (r / 32)` and that lane plus 32 (the
  pair of warps 0 and 1 holds rows 0 to 31, the pair of warps 2 and 3 rows 32 to 63). `.32x128b`
  copies 32 rows of 16 bytes, row `r` to lanes `r`, `r + 32`, `r + 64` and `r + 96`. `.4x256b`
  copies 4 rows of 32 bytes, row `r` to lane `32 r`, the first lane of each warp's chunk. With
  `.cta_group::2` the copy is made in the pair's even and odd CTA alike, each from its own shared
  memory at the descriptor's offset to its own Tensor Memory at the address; the bytes read are
  recorded CTA by CTA, the even CTA's first.

### EXT-TCCP — the row and lane maps and the decompression of tcgen05.cp

Statement: The model makes two readings of `tcgen05.cp`. (1) Row r of the canonical source layout of
  a `tcgen05.cp` is the Tensor Memory lanes its shape and multicast assign to r, with the row's
  bytes as the lane's bits in order, as CUTLASS numbers them, and a `.cta_group::2` copy reads each
  CTA's shared memory at the same descriptor offset. (2) For a decompressing `tcgen05.cp`, element
  `i` (`i < 16`) of a 16-byte source chunk is bits `4 i` to `4 i + 3` (`.b4x16_p64`) or `6 i` to
  `6 i + 5` (`.b6x16_p32`) of the chunk read as a little-endian number, and it is written to
  destination byte `i` of the chunk's 16 bytes, shifted left by 2 bits for 4-bit elements and
  unshifted for 6-bit elements, with zeros in the other bits. Destination byte `i` is
  `((X >> 4 i) % 16) * 4` for `.b4x16_p64` and `(X >> 6 i) % 64` for `.b6x16_p32`, where `X` is the
  little-endian value of the chunk's 16 source bytes.

Source:
- §9.7.18.9.1.1
- §9.7.18.9.1.2 and Figures 197 to 201

Why it is not spec text: (1) The ISA names the shapes (lanes x bits), says that the warps of a pair
  each receive half of the data and that `.warpx4` sends the data to all four warps, and that the
  source is described by a matrix descriptor, without a textual element map. CUTLASS
  (`include/cute/atom/copy_traits_sm100.hpp`) numbers source bits as
  `[core_matrix_strided, core_matrix_leading]` with Tensor Memory strides `(DP, 1)` for
  `SM100_UTCCP_128dp256bit_1cta` and `SM100_UTCCP_128dp128bit_1cta`, adds a broadcast mode of stride
  `64 DP` for `SM100_UTCCP_2x64dp128bitlw0213_1cta`, a repeat mode of stride `64 DP` and a broadcast
  mode of stride `32 DP` for `SM100_UTCCP_2x64dp128bitlw0123_1cta`, and a broadcast mode of stride
  `32 DP` for `SM100_UTCCP_4x32dp128bit_1cta`; the `_2cta` forms use the same map for both CTAs. The
  maps above are these. (2) The text says that 16 packed elements become 16 bytes and leaves the
  rest to the figures. Figure 198 (`_images/tcgen05-decompression-4b8b-individual.png`) draws the
  fields S, E2 and M1 of a 4-bit element in bits 5 to 2 of the byte with bits 7, 6, 1 and 0 zero;
  Figures 200 and 201 (`_images/tcgen05-decompression-6b8b-individual1.png` and
  `_images/tcgen05-decompression-6b8b-individual2.png`) draw the E3M2 and E2M3 fields of a 6-bit
  element in bits 5 to 0 with bits 7 and 6 zero. Figures 197 and 199 draw the packed elements of a
  chunk and their bytes in the same left-to-right order, without bit numbers. The model reads the
  packed elements from the least significant bit up.

Evidence: (1) The manual gives the shapes, the warp pairs and the `.warpx4` broadcast in the
  sentences quoted in THREAD-TC-CP-CELLS and no element map. In CUTLASS (NVIDIA/cutlass) commit
  b2f249ac (v4.8.0-23; the ValID layouts named above in include/cute/atom/copy_traits_sm100.hpp)
  every row of the five shapes goes to the lanes `TcCpShape.lanes` gives, as the host script
  txverify-archive/core-coverage/probes/cutlass_check.py checks. The hardware probe
  txverify-archive/core-coverage/probes/tcgen05_cp/ compares every Tensor Memory byte with this map
  for each shape, `.cta_group::1` and `::2`, and five descriptors (no swizzle with two LBO/SBO
  pairs, and the 32-, 64- and 128-byte swizzles). It ran on a B200 on 2026-11-16 and agreed with
  this map in every byte of every case. For `.4x256b` the manual says only that the copy moves 4
  lanes of 256 bits. In the same CUTLASS commit `Copy_Traits<SM100_UTCCP_4dp256bit_1cta>` (and
  `_2cta`, with the same `ValID`) has `ValID = Layout<Shape<_128, _256>, Stride<DP_b, _1>>` and
  `SrcLayout = DstLayout = Layout<Shape<_1, Shape<_4, _256>>, Stride<_0, Stride<_32, _128>>>`, which
  put bit `b` of source row `r` at logical bit `32 r + 128 b`, that is lane `32 r` and bit `b`; the
  model takes this map (`TcCpShape.lanes .s4x256b r = [32 r]`). The comment of that trait says that
  the copy refreshes `the last 4 lanes of each tmem subpartition`, which disagrees with its layout;
  the layout is taken. The probes txverify-archive/core-coverage/probes/tcgen05_cp/ (which prints
  the lanes `.4x256b` writes) and txverify-archive/core-coverage/probes/tcgen05_cp_ext/ (which
  compares every byte with `[32 r]` for both CTA groups and three descriptors) ran on a B200 on
  2026-11-16 and found that the copy writes lanes 0, 32, 64 and 96 with row `r` in lane `32 r`, as
  the layout and the model say; the trait's comment is wrong. (2) (manual) the figures above.
  (CUTLASS) CUTLASS (NVIDIA/cutlass) commit b2f249ac (v4.8.0-23) has no `tcgen05.cp` atom with
  decompression; its sub-byte arrays (include/cutlass/array_subbyte.h) keep element `i` at bit
  `i * sizeof_bits` of the storage, the order the model takes for the packed elements. (B200) The
  probe txverify-archive/core-coverage/probes/tcgen05_cp_ext/ compares every destination byte of
  decompressing copies with this map. It ran on a B200 on 2026-11-16 and agreed for `.128x128b` and
  `.128x256b` with both formats, two descriptors and four random seeds each.

Direction: reading

Effect: The Tensor Memory cells a `tcgen05.cp` writes and the bytes they hold are fixed by these
  maps. If the hardware map differs, the values a later load or MMA reads differ from the ones
  proven. If the hardware ordered the packed elements of a decompressing copy or placed their bits
  otherwise, the bytes that the copy leaves in Tensor Memory, and every value computed from them,
  would differ from the model's. Disclosed by every kernel whose statement names `Op.tcCp`:
  FlashMlaSparseDecodeH64.
-/

/-- Source rows of a copy. -/
def _root_.PTX.TcCpShape.rows : TcCpShape → Nat
  | .s128x256b | .s128x128b => 128
  | .s64x128b _ => 64
  | .s32x128b => 32
  | .s4x256b => 4

/-- Bytes of one source row: 32 for 256 bits, 16 for 128 bits. -/
def _root_.PTX.TcCpShape.rowBytes : TcCpShape → Nat
  | .s128x256b | .s4x256b => 32
  | _ => 16

/-- Bytes a copy reads from one CTA's shared memory. -/
def _root_.PTX.TcCpShape.sourceBytes (s : TcCpShape) : Nat := s.rows * s.rowBytes

/-- The Tensor Memory lanes of source row `r` (EXT-TCCP). -/
def _root_.PTX.TcCpShape.lanes : TcCpShape → Nat → List Nat
  | .s128x256b, r | .s128x128b, r => [r]
  | .s64x128b true, r => [r, r + 64]
  | .s64x128b false, r => [r % 32 + 64 * (r / 32), r % 32 + 64 * (r / 32) + 32]
  | .s32x128b, r => [r, r + 32, r + 64, r + 96]
  | .s4x256b, r => [32 * r]

/-- An issued copy: the Tensor Memory address, the decoded source descriptor, the shape, the
CTAs that copy, the even CTA first, and the decompression. -/
structure Spec where
  address : Nat
  src : TcShared.Descriptor
  shape : TcCpShape
  ctas : List Nat
  fmt : Option TcCpFmt := none
  deriving DecidableEq, Repr

/-- Lane field 0 and the shape's columns within the physical columns. -/
def AddressOk (s : TcCpShape) (address : Nat) : Prop :=
  address / 2 ^ 16 = 0 ∧ address % 2 ^ 16 + s.rowBytes / 4 ≤ 512

instance addressOkDecidable (s : TcCpShape) (address : Nat) : Decidable (AddressOk s address) := by
  unfold AddressOk; infer_instance

/-- The shared location of source byte `index` of a copy of shape `s` from descriptor `src` in CTA
`cta`: byte `index % rowBytes` of row `index / rowBytes` of the K-major canonical layout of
one-byte elements. -/
def byteLoc (s : TcCpShape) (src : TcShared.Descriptor) (cta index : Nat) : Option Loc :=
  if index < s.sourceBytes then
    (TcShared.byteAddress 1 .k src (index / s.rowBytes) (index % s.rowBytes) 0).map
      fun a => ⟨.shared, cta, a⟩
  else none

/-- The Tensor Memory word at lane `lane` that source byte `index` of a copy of shape `s` lands
in. -/
def cell (s : TcCpShape) (address cta lane index : Nat) : TcMma.Cell :=
  ⟨cta, address / 2 ^ 16 + lane, address % 2 ^ 16 + index % s.rowBytes / 4⟩

/-- A recorded byte as a one-byte value with the same content. -/
def byteValue (b : Byte) : Value := .slice b.1 b.2 1

/-- The word of row `row`, column `col` of a copy of shape `s` from the bytes recorded from one
CTA: its four bytes in order, if all known. -/
def word (s : TcCpShape) (bytes : List (Option Byte)) (row col : Nat) : Option Value := do
  let b0 ← bytes.getD (row * s.rowBytes + 4 * col) none
  let b1 ← bytes.getD (row * s.rowBytes + 4 * col + 1) none
  let b2 ← bytes.getD (row * s.rowBytes + 4 * col + 2) none
  let b3 ← bytes.getD (row * s.rowBytes + 4 * col + 3) none
  pure (.pair (.pair (byteValue b0) (byteValue b1)) (.pair (byteValue b2) (byteValue b3)))

end PTX.TcCopy

namespace PTX.TcShift

/-! ## THREAD-TC-SHIFT-CELLS — the Tensor Memory cells of tcgen05.shift
Statement: A `tcgen05.shift` moves, in each CTA of its group and in each 32-lane chunk of the Tensor
  Memory, the 32 bytes (8 columns from the address's column) of lanes 1 to 31 of the chunk to the
  lane below; lane 31 of the chunk is not written and keeps its word. The address must have lane
  field 0 and its 8 columns within the 512 physical ones.

Defs: TcShift.Spec, TcShift.AddressOk, TcShift.addressOkDecidable, TcShift.Spec.cell,
  TcShift.Spec.Writes, TcShift.Spec.Reads, TcShift.source

Source:
- §9.7.18.9.3: "Instruction tcgen05.shift is an asynchronous instruction which initiates the
    shifting of 32-byte elements downwards across all the rows, except the last, by one row."
- §9.7.18.9.3: "The address operand taddr specifies the base address of the matrix in the Tensor
    Memory whose rows must be down shifted."
- §9.7.18.9.3: "When .cta_group::1 is specified, the shift operation is performed in the Tensor
    Memory of the current CTA."
- §9.7.18.9.3: "When .cta_group::2 is specified, the shift operation is performed in the Tensor
    Memory of both the current and the peer CTAs ."
- §9.7.18.2.3 (the shape `.31x256b (implicit)` of `.shift`)
- EXT-TCSHIFT

Direction: reading

Applies: tcgen05.shift.cta_group::{1,2}.down

Premises: A Tensor Memory address with lane field 0 and columns `c` to `c + 7` within 512; with
  `.cta_group::2`, the pair's CTAs in the launch.

Effect: Cell geometry only; issue, completion, values and ordering are THREAD-TC and
  DEP-TMEM-SHIFT-VALUE. Lane `32 w + i` (i < 31) receives lane `32 w + i + 1`'s word in each of the
  8 columns (`source`). Lane `32 w + 31` is outside `Spec.Writes`, so a later read of it takes the
  word of the write before the shift.

### EXT-TCSHIFT — the rows and lanes of tcgen05.shift

Statement: The model takes the rows of `tcgen05.shift` to be the lanes of each 32-lane chunk of the
  Tensor Memory and the 32-byte element to be 8 columns starting at the address's column.
  `tcgen05.shift.cta_group::N .down [taddr]` with lane field 0 moves, in every 32-lane chunk `32 w`
  to `32 w + 31` (w < 4) and in columns `c` to `c + 7` (`c` the column field of `taddr`), lane
  `32 w + i + 1` to lane `32 w + i` for `i` from 0 to 30; lane `32 w + 31` is the last row, which
  the text excludes from the shift, and keeps its word.

Source:
- §9.7.18.9.3 and §9.7.18.2.3 (shape `.31x256b (implicit)`)

Why it is not spec text: The text says that 32-byte elements of all rows but the last move down by
  one row and that the implicit shape is 31 x 256 bits; it does not say whether a row is a lane of
  the whole 128-lane matrix or of a 32-lane chunk, which lanes take part for a nonzero lane field,
  or whether moving down takes a row to a lower or a higher lane index. Thirty-one moved rows of
  256 bits per 32-lane chunk agree with the shape.

Direction: reading

Effect: If the hardware moved other lanes, the cells that a shift writes and the values it leaves
  would differ from the model's. Disclosed by every kernel whose statement names `Op.tcShift`: none.

Evidence: (manual) the sentences above; there is no figure. (CUTLASS) CUTLASS (NVIDIA/cutlass)
  commit b2f249ac (v4.8.0-23) issues no `tcgen05.shift`. (B200) The probe
  txverify-archive/core-coverage/probes/tcgen05_shift/ prints, for each destination lane, the source
  lane it holds after a shift with lane field 0 and 32 and two column fields. It ran on a B200 on
  2026-11-16: in every 32-lane chunk, lane `32 w + i` (i < 31) received the old word of lane
  `32 w + i + 1` in columns `c` to `c + 7`, lane `32 w + 31` kept its old word, and no other cell
  changed. The result was the same for lane field 0 and 32, for column fields 0 and 8, and in both
  CTAs of `.cta_group::2`. The probe decided the direction and the chunk structure of this reading,
  and it agrees with the text that the last lane of each chunk keeps its word.
-/

/-- An issued shift: the Tensor Memory address and the CTAs of its group, the even CTA first. -/
structure Spec where
  address : Nat
  ctas : List Nat
  deriving DecidableEq, Repr

/-- Lane field 0 and the 8 columns within the physical columns. -/
def AddressOk (address : Nat) : Prop :=
  address / 2 ^ 16 = 0 ∧ address % 2 ^ 16 + 8 ≤ 512

instance addressOkDecidable (address : Nat) : Decidable (AddressOk address) := by
  unfold AddressOk; infer_instance

/-- Lane `lane`, column `col` (from the address's column) of the shift in CTA `cta`. -/
def Spec.cell (s : Spec) (cta lane col : Nat) : TcMma.Cell := ⟨cta, lane, s.address % 2 ^ 16 + col⟩

/-- The shift writes `c`: lanes 0 to 30 of a chunk, in one of its 8 columns, in a CTA of its
group. The last lane of each chunk keeps its word. -/
def Spec.Writes (s : Spec) (c : TcMma.Cell) : Prop :=
  ∃ cta lane col, cta ∈ s.ctas ∧ lane < 128 ∧ lane % 32 < 31 ∧ col < 8 ∧ c = s.cell cta lane col

/-- The shift reads `c`: lanes 1 to 31 of a chunk, in one of its 8 columns. -/
def Spec.Reads (s : Spec) (c : TcMma.Cell) : Prop :=
  ∃ cta lane col, cta ∈ s.ctas ∧ lane < 128 ∧ 0 < lane % 32 ∧ col < 8 ∧ c = s.cell cta lane col

/-- The cell whose old word the shift moves into a cell `c` it writes: the next lane, which for a
written cell (lanes 0 to 30 of a chunk) lies in the same chunk. -/
def source (c : TcMma.Cell) : TcMma.Cell := ⟨c.cta, c.lane + 1, c.column⟩

end PTX.TcShift
