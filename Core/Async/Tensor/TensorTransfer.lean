-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fintype.Prod

@[expose] public section

namespace PTX.TensorTransfer

/-! ## THREAD-TENSOR-TRANSFER-MAP — byte correspondence for a tensor load
Statement: Each element byte that a tensor transfer selects has a swizzled shared destination and
  either an in-bounds global source or the descriptor's out-of-bounds fill. Shared padding is not
  copied, and the byte count includes out-of-bounds elements. With four-row coordinates, box row
  `r` is tensor row `rows r`, starting at the column of the origin.

Defs: TensorTransfer.Slot, TensorTransfer.slotAt, TensorTransfer.Source, TensorTransfer.index,
  TensorTransfer.coord, TensorTransfer.bytes, TensorHasOob, tensorHasOobDecidable

Source:
- §5.5.3
- §5.5.3.4 (`.tile::gather4`)
- §5.5.7
- §9.7.10.28.5.3 (cp.async.bulk.tensor)
- EXT-TMA-GEOMETRY

Direction: reading

Applies: Non-interleaved 1D–5D tiled transfers and 2D `.tile::gather4`/`.tile::scatter4` transfers
  with the represented descriptor formats

Premises: Descriptor and instruction validity, storage, publication and allocation are checked by
  the consuming instruction rules. Each slot denotes one selected element byte.

Effect: An address/value-source map, without a trace order. `TensorHasOob` holds when some selected
  element is out of bounds. The four-row coordinates are the readings EXT-TMA-GATHER4 and
  EXT-TMA-SCATTER4, and the shared layout of such a box is the tile layout of the box. Slot
  coordinates are selected-element indices, distinct from tensor coordinates: the inner index, the
  row (the outer axes' indices in mixed radix, `TensorTile.indexOf`) and the element byte. The fill
  source is symbolic: OOB-NaN is not silently identified with a real number or zero. The byte count
  includes OOB-filled elements but excludes shared padding.

### EXT-TMA-GATHER4 — the four rows of `.tile::gather4`

Statement: The four rows that a `.tile::gather4` load requests are placed in shared memory as the
  tile layout of the map's box with four rows, where row `j` is tensor row `y_j` starting at
  column `x`.

Source:
- §5.5.3.4: "combined to form single 2D destination tensor"

Why it is not spec text: §5.5.3.4 says the four request coordinates form four bounding boxes (box
  dimension 1 must be one) that are combined to form a single 2D destination tensor, and it gives
  no destination layout. The model reads the destination as the tile layout of the map's box with
  four rows, in which row `j` is tensor row `y_j` from column `x`.

Evidence: On a B200 `Tools/probes/tma_gather4.ptx` (2D u8 map, 8 KiB sentinel-filled buffer)
  matched, in every byte, that layout: no/32B/64B/128B swizzles, destination offsets 0 to 1024
  (128-byte phases), rows narrower than the swizzle width, repeated and descending rows and per-row
  out-of-bounds zero fill; the mbarrier completed with `4 * box width` bytes. With
  `.multicast::cluster` (`Tools/probes/tma_mc_gather4.ptx`, one 4-CTA cluster, masks 0xF, 0x5, 0xA,
  0xE, 0x1) every masked CTA received this layout and its mbarrier completed with `4 * box width`
  bytes; unmasked CTAs were untouched. Box dimension 1 of 2 or 4, or an inner start that is not
  16-byte aligned, fails with an illegal instruction.

Direction: reading

Effect: The destination layout of a gather4 load is fixed by this row-to-tile map; if the hardware
  layout differs, the loaded shared bytes differ from the ones proven. Disclosed by every kernel
  whose statement names `Op.cpTensor (mode := TensorMode.fourRows)` or
  `Op.prefetchTensor (mode := TensorMode.fourRows)`: FlashMlaSparseDecodeH64.

### EXT-TMA-SCATTER4 — the four rows of `.tile::scatter4`

Statement: A `.tile::scatter4` store reads the tile layout of the map's box with four rows from
  shared memory and writes it as four tensor rows, where box row `j` is tensor row `y_j` starting
  at column `x`.

Evidence: On a B200 `Tools/probes/tma_scatter4.ptx` (2D u8 map, pattern-filled shared source,
  sentinel-filled tensor) matched, in every tensor byte, this store: no/32B/64B/128B swizzles,
  source offsets 0 to 1024, padded rows, and rows or columns past the extent unwritten. A negative
  column or row coordinate, box dimension 1 of 2 or an unaligned inner start fails with an illegal
  instruction; a 64-byte-aligned source is misaligned. With a repeated row the later row's bytes
  were stored (one case); the model leaves the order of the two writes to the memory rules.

Direction: reading

Effect: The source layout and the written tensor rows of a scatter4 store are fixed by this map; if
  the hardware map differs, the stored tensor differs from the one proven. Disclosed by every kernel
  whose statement names `Op.cpTensorStore (mode := TensorMode.fourRows)`: none.
-/
/-- One byte of one element that a tensor box selects: the element's column, its row (the
combination of its outer-axis indices) and the byte within the element. -/
abbrev Slot {outer : Nat} (d : TensorDescriptor.Descriptor outer) :=
  Fin (TensorTile.count d.box 0) × Fin (TensorTile.rows d.box) × Fin d.format.bytes

/-- The slot of selected element `(x, y)` (column, row) and element byte `byte`, if in range. -/
def slotAt {outer : Nat} (d : TensorDescriptor.Descriptor outer) (x y byte : Nat) :
    Option (Slot d) :=
  if hx : x < TensorTile.count d.box 0 then
    if hy : y < TensorTile.rows d.box then
      if hb : byte < d.format.bytes then some ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨byte, hb⟩⟩
      else none
    else none
  else none

/-- Where a byte of a tensor load comes from: a global address, or the out-of-bounds fill of the
descriptor for a byte of the given format. -/
inductive Source where
  | global (address : Nat)
  | fill (mode : TensorDescriptor.Fill) (format : TensorDescriptor.Format) (byte : Nat)
  deriving DecidableEq, Repr

/-- The per-axis element indices of the element of a slot. -/
def index {outer : Nat} {d : TensorDescriptor.Descriptor outer} (slot : Slot d) :
    Fin (outer + 1) → Nat :=
  TensorTile.indexOf d.box slot.1.val slot.2.1.val

/-- The global coordinate of a slot's element: `origin + index * traversal` (tile mode), or with
gather4 row coordinates `rows`, column `origin 0 + index 0` of tensor row `rows r` for box row `r`
(only the two axes of a 2D map exist then). -/
def coord {outer : Nat} (d : TensorDescriptor.Descriptor outer) (origin : Fin (outer + 1) → Int)
    (rows : Option (Fin 4 → Int)) (slot : Slot d) : Fin (outer + 1) → Int :=
  match rows with
  | none => TensorTile.coord d.box origin (index slot)
  | some ys => fun axis =>
    if axis.val = 0 then origin axis + slot.1.val else
      ys ⟨slot.2.1.val % 4, Nat.mod_lt _ (by decide)⟩


/-- The number of bytes a tensor transfer moves: the selected elements times the element size,
including out-of-bounds elements and excluding shared padding. -/
def bytes {outer : Nat} (d : TensorDescriptor.Descriptor outer) : Nat :=
  TensorTile.count d.box 0 * TensorTile.rows d.box * d.format.bytes

end PTX.TensorTransfer

namespace PTX

/-- Some element the transfer selects is outside the tensor (§5.5.3.3). -/
def TensorHasOob {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int)
    (rows : Option (Fin 4 → Int)) : Prop :=
  ∃ slot : TensorTransfer.Slot d,
    ¬ TensorAddress.InBounds (TensorDescriptor.geometry d) (TensorTransfer.coord d origin rows slot)

instance tensorHasOobDecidable {outer : Nat} (d : TensorDescriptor.Descriptor outer)
    (origin : Fin (outer + 1) → Int) (rows : Option (Fin 4 → Int)) :
    Decidable (TensorHasOob d origin rows) := by
  unfold TensorHasOob TensorAddress.InBounds
  infer_instance

end PTX
