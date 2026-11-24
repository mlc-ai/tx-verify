-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorAddress
public import Core.Async.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.TensorTile

/-! ## THREAD-TENSOR-TILE — tiled bounding-box traversal
Statement: Along the innermost axis a bounding box selects consecutive elements, and along every
  other axis it selects the elements at the origin plus index times the traversal stride. Each
  axis contributes the box size divided by the traversal stride, rounded up. Whether a selected
  element lies inside the tensor is checked separately.

Defs: TensorTile.Box, TensorTile.step, TensorTile.count, TensorTile.coord, TensorTile.source,
  TensorTile.rowsOf, TensorTile.unflatten, TensorTile.rows, TensorTile.indexOf

Source:
- §5.5.3.1–§5.5.3.3
- CUDA Driver API cuTensorMapEncodeTiled (boxDim and elementStrides)
- EXT-TMA-GEOMETRY

Direction: reading

Applies: Non-interleaved tiled tensor accesses with byte-sized elements

Premises: Descriptor validity checks box sizes and traversal strides. Indices enumerate selected
  elements. They enumerate no skipped elements and no shared padding.

Effect: Selected-element geometry and global source addresses. A valid descriptor's dimension-0
  traversal stride is one (THREAD-TENSOR-DESCRIPTOR, §5.5.3.2), so `step` is the traversal stride on
  every axis of a valid box. Legality and host encoding remain separate from this geometry.
-/
/-- A bounding box of `rank` axes: for each axis, the number of elements it spans and the traversal
stride with which elements are selected. -/
structure Box (rank : Nat) where
  size : Fin rank → Nat
  traversal : Fin rank → Nat

/-- The traversal stride of an axis: one for the innermost axis and the box's stride otherwise. -/
def step {rank : Nat} (b : Box rank) (axis : Fin rank) : Nat :=
  if axis.val = 0 then 1 else b.traversal axis

/-- The number of elements the box selects on an axis: its size divided by the traversal stride,
rounded up. -/
def count {rank : Nat} (b : Box rank) (axis : Fin rank) : Nat :=
  (b.size axis + step b axis - 1) / step b axis

/-- The global coordinate of the selected element with per-axis indices `index`: the origin plus the
index times the traversal stride. -/
def coord {rank : Nat} (b : Box rank) (origin : Fin rank → Int)
    (index : Fin rank → Nat) : Fin rank → Int :=
  fun axis => origin axis + (index axis * step b axis : Nat)

/-- Outer none: not a selected element/byte. Inner none: selected but outside tensor. -/
def source {rank : Nat} (d : TensorAddress.Geometry rank) (b : Box rank)
    (origin : Fin rank → Int) (index : Fin rank → Nat) (byte : Nat) :
    Option (Option Nat) :=
  if (∀ axis, index axis < count b axis) ∧ byte < d.elementBytes then
    some (TensorAddress.lookup d (coord b origin index) byte)
  else none

/-- The number of mixed-radix values with digit bounds `c`: `c 0 * c 1 * …` (one digit is
`c 0` itself, so a two-dimensional box's row count is its outer count). -/
def rowsOf : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 1
  | 1, c => c 0
  | k + 2, c => c 0 * rowsOf (k + 1) (fun i => c i.succ)

/-- Digit `i` of `r` in the mixed radix `c`, least significant first (one digit is `r`). -/
def unflatten : (k : Nat) → (Fin k → Nat) → Nat → Fin k → Nat
  | 0, _, _ => Fin.elim0
  | 1, _, r => fun _ => r
  | k + 2, c, r => Fin.cases (r % c 0) (unflatten (k + 1) (fun i => c i.succ) (r / c 0))

/-- Rows of a box: the selected-element combinations of its outer axes. -/
def rows {outer : Nat} (b : Box (outer + 1)) : Nat :=
  rowsOf outer (fun axis => count b axis.succ)

/-- Element indices of a selected element: column `column` of row `row` (outer axes in mixed
radix, axis 1 least significant). -/
def indexOf {outer : Nat} (b : Box (outer + 1)) (column row : Nat) : Fin (outer + 1) → Nat :=
  Fin.cases column (unflatten outer (fun axis => count b axis.succ) row)

/-! ## THREAD-TENSOR-TILE-SHARED — tiled shared layout
Statement: The selected rows of a box, which are the combinations of its outer axes with axis 1
  varying fastest, are packed in shared memory with a pitch equal to the inner box byte size, padded
  up to the swizzle width when the box is narrower. The swizzle permutation is applied to the
  physical byte offset with the phase of the actual shared base address. Padding bytes are neither
  written nor counted.

Defs: TensorTile.swizzleWidth, TensorTile.rowBytes, TensorTile.linearByte, TensorTile.sharedByte

Source:
- §5.5.3 (tiled mode)
- §5.5.7 (swizzling)
- CUDA Programming Guide §4.13.2 (inner dimension padding and Table 27)
- EXT-TMA-GEOMETRY

Direction: reading

Applies: Non-interleaved 1D–5D tiled copies with byte-sized elements and 16-byte-atom swizzles

Premises: The consuming instruction checks descriptor legality, shared base alignment, selected
  indices and byte bounds. For a nonzero swizzle, the inner box byte size is at most its swizzle
  width.

Effect: Shared address geometry only. Padding bytes are not selected copy elements and are not
  implicitly initialized.

Review: `Tools/probes/tma2d.ptx` loads 2D u8 boxes on a B200 into a sentinel-filled shared
  buffer: for no/32B/64B/128B swizzles, destination offsets 0..1024 (all 128-byte phases used),
  inner boxes narrower than the swizzle width (padded rows) and out-of-bounds origins, every
  byte of the 8 KiB buffer matched this layout, the zero fill and untouched padding.

### EXT-TMA-GEOMETRY — tiled tensor geometry and descriptor limits from the CUDA Driver API

Statement: The global address of an element is the base plus, over the axes, the coordinate times
  the stride, with the first stride the element size. Axis 0 has unit traversal, and axis `i` of a
  box selects `origin + index * traversalStride_i`, each axis contributing
  `ceil(boxDim_i / traversalStride_i)` elements. The selected rows of a box (the combinations of the
  outer axes, axis 1 fastest) are packed in shared memory with a pitch equal to the inner box byte
  size, padded up to the swizzle width when the box is narrower, the padding being neither written
  nor counted. The `complete-tx` byte count is the selected elements including out-of-bounds fill
  and excluding padding. Descriptors outside the numeric limits of the CUDA Driver API are
  rejected: extents at most 2^32, strides multiples of 16 below 2^40, box sizes at most 256,
  traversal strides at most 8, inner box byte size a multiple of 16, a tensor map object 64-byte
  aligned and a shared tile 128-byte aligned.

Source:
- CUDA Driver API 13.2.1 `cuTensorMapEncodeTiled` (`boxDim`, `elementStrides`, `globalStrides`,
    `globalDim`)
- CUDA C++ Programming Guide §4.13.2 (inner dimension padding, Table 27)
- §5.5.1 (strides specify padding)
- §5.5.3.1 (bounding box), Figure 8 (address formula)
- §5.5.7 (swizzling: the base offset formula uses `(dstMem / 128)`, so it does not require a
    128-byte aligned tile)
- §5.5.8 (the tensor map object is 128 bytes)

Why it is not spec text: The PTX text gives dimensions, strides and the bounding box in prose and
  figures but no coordinate-to-address formula, no traversal-stride element count, no shared pitch
  or padding rule, no `complete-tx` count for out-of-bounds or padded elements and none of the
  numeric limits; those are properties of the host API that creates the descriptor. The 64-byte
  alignment of the map object and the 128-byte alignment of a shared tile have no text at all
  (§5.5.8 gives the map's size, 128 bytes).

Evidence: `Tools/probes/tma2d.ptx` (2D u8 boxes on a B200: swizzles, offsets, padded rows and
  out-of-bounds origins matched every byte of the model's layout). The geometry for more than two
  axes, a traversal stride above one and the `complete-tx` count of padded or out-of-bounds elements
  is not probed.

Direction: reading

Effect: Reading for the geometry (it decides which bytes move and where); stricter for the limits
  (they only reject descriptors and issues). Disclosed by every kernel whose statement names
  `Op.cpTensor`, `Op.cpTensorStore` or `Op.prefetchTensor`: FlashAttn4Fwd, FlashMlaSparseDecodeH64,
  Fp16Gemm8192, InklingRelDecode.
-/
/-- The width in bytes to which a swizzle mode pads a tile row: 0, 32, 64 or 128. -/
def swizzleWidth : TensorSwizzle.Mode → Nat
  | .none => 0
  | .b32 => 32
  | .b64 => 64
  | .b128 => 128

/-- The pitch of a tile row in shared memory: the inner box byte size, or the swizzle width if that
is larger. -/
def rowBytes {outer : Nat} (b : Box (outer + 1)) (elementBytes : Nat) (mode : TensorSwizzle.Mode) :
    Nat :=
  max (count b 0 * elementBytes) (swizzleWidth mode)

/-- The byte offset, before swizzling, of byte `byte` of the element at `column` of row `row` of the
tile. -/
def linearByte {outer : Nat} (b : Box (outer + 1)) (elementBytes : Nat) (mode : TensorSwizzle.Mode)
    (column row byte : Nat) : Nat :=
  row * rowBytes b elementBytes mode + column * elementBytes + byte

/-- The shared address of byte `byte` of the element at `column` of row `row` of a tile based at
`base`: the base plus the swizzled offset of the byte. -/
def sharedByte {outer : Nat} (b : Box (outer + 1)) (elementBytes : Nat) (mode : TensorSwizzle.Mode)
    (base column row byte : Nat) : Nat :=
  base + TensorSwizzle.offset mode base (linearByte b elementBytes mode column row byte)

end PTX.TensorTile
