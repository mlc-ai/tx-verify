-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorTile

@[expose] public section

namespace PTX.TensorDescriptor

/-! ## THREAD-TENSOR-DESCRIPTOR — non-interleaved tiled descriptor properties
Statement: A tensor map is accepted only if it obeys the limits of the host API. It has at most
  five axes and a 16-byte aligned base address. Its extents are positive and at most 2^32, and
  its outer strides are multiples of 16 below 2^40. Its box sizes are positive and at most 256, its
  traversal strides are positive and at most 8 with the innermost one equal to one, and the inner
  box byte size is a multiple of 16 that fits within the swizzle width. The NaN fill is allowed
  only for floating-point element types.

Defs: TensorDescriptor.Format, TensorDescriptor.Format.bytes, TensorDescriptor.Format.floating,
  TensorDescriptor.Fill, TensorDescriptor.AllocationClass, TensorDescriptor.Descriptor,
  TensorDescriptor.geometry, TensorDescriptor.Valid, TensorDescriptor.validDecidable,
  TensorDescriptor.Descriptor.fourRows, TensorDescriptor.BoxAligned,
  TensorDescriptor.boxAlignedDecidable

Source:
- CUDA Driver API 13.2.1 `cuTensorMapEncodeTiled`
- §5.5.1
- §5.5.3 (§5.5.3.2: dimension-0 traversal stride)
- §5.5.7
- EXT-TMA-GEOMETRY (the numeric limits)

Direction: scope

Applies: Non-interleaved tiled descriptors with ordinary byte-sized integer/floating types and
  16-byte-atom swizzle modes

Premises: Host encoding or descriptor-update semantics must supply these properties for the actual
  opaque descriptor used by the instruction.

Effect: Descriptor property validation. The innermost traversal stride is one because §5.5.3.2
  says "For non-interleaved layout, the traversal stride in dimension 0 must always be 1".
  `BoxAligned` is the 16-byte alignment of a box's global start (§5.5.3.1). It is a property of the
  instruction's coordinates. Unsupported descriptor formats (sub-byte packing, FTZ/TF32 conversion,
  interleaved, im2col and other swizzle atomicities) are not represented as ordinary copies. The
  first byte stride is implicit in the host API and derived from the format here. No monotonic
  ordering of the remaining strides is assumed: split-axis layouts can have a smaller outer stride.
  Descriptor-storage alignment and address arithmetic bounds are instruction/access checks, not
  guarantees of this property record.

### EXT-TMA-BOX-ALIGN — a misaligned box start traps

Statement: A tensor load, store or prefetch whose bounding box starts at a global address that is
  not 16-byte aligned is a fault.

Source:
- §5.5.3.1 (16-byte alignment of the bounding box's address)

Evidence: On a B200, 2D u8 tiled loads (`Tools/probes/tma2d.ptx`) and stores
  (`Tools/probes/tma2d_store.ptx`) with inner coordinate 4 or 8 fail with an illegal instruction,
  with or without swizzle, while 0, 16, 32, 48 and -16 complete.

Direction: stricter

Effect: A start that is not 16-byte aligned is a fault of the model, as it is on the probed
  hardware; the aligned starts are accepted as the text states. Disclosed by every kernel whose
  statement names `Op.cpTensor`, `Op.cpTensorStore` or `Op.prefetchTensor`: FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode.
-/
/-- The element type of a tensor map. -/
inductive Format where
  | u8 | u16 | u32 | s32 | u64 | s64 | f16 | bf16 | f32 | f64
  deriving DecidableEq, Repr

def Format.bytes : Format → Nat
  | .u8 => 1
  | .u16 | .f16 | .bf16 => 2
  | .u32 | .s32 | .f32 => 4
  | .u64 | .s64 | .f64 => 8

def Format.floating : Format → Bool
  | .f16 | .bf16 | .f32 | .f64 => true
  | _ => false

/-- The value written for an out-of-bounds element of a tensor load: zero, or NaN (floating-point
element types only). -/
inductive Fill where
  | zero | oobNan
  deriving DecidableEq, Repr

/-- Allocation-class metadata is part of the actual opaque tensor map. -/
inductive AllocationClass where
  | small | large
  deriving DecidableEq, Repr

/-- A tiled tensor map of `outer + 1` axes: the element format, the global base address, the extent
of each axis, the byte strides of the outer axes, the bounding box, the swizzle mode, the
out-of-bounds fill and the allocation class. -/
structure Descriptor (outer : Nat) where
  format : Format
  base : Nat
  extent : Fin (outer + 1) → Nat
  outerStride : Fin outer → Nat
  box : TensorTile.Box (outer + 1)
  swizzle : TensorSwizzle.Mode
  fill : Fill
  allocationClass : AllocationClass

/-- The global tensor geometry that the descriptor defines; the stride of the first axis is the
element size. -/
def geometry {outer : Nat} (d : Descriptor outer) : TensorAddress.Geometry (outer + 1) :=
  ⟨d.base, d.format.bytes, d.extent, Fin.cases d.format.bytes d.outerStride⟩

/-- The descriptor obeys the limits of the host API that creates tensor maps: rank, alignment,
extents, strides, box sizes, traversal strides, swizzle fit and fill mode. -/
def Valid {outer : Nat} (d : Descriptor outer) : Prop :=
  outer < 5 ∧ d.base % 16 = 0 ∧
  (∀ i, 0 < d.extent i ∧ d.extent i ≤ 2 ^ 32) ∧
  (∀ i, d.outerStride i % 16 = 0 ∧ d.outerStride i < 2 ^ 40) ∧
  (∀ i, 0 < d.box.size i ∧ d.box.size i ≤ 256) ∧
  (∀ i, 0 < d.box.traversal i ∧ d.box.traversal i ≤ 8) ∧
  (d.box.size 0 * d.format.bytes) % 16 = 0 ∧
  (d.swizzle = .none ∨ d.box.size 0 * d.format.bytes ≤ TensorTile.swizzleWidth d.swizzle) ∧
  (d.fill = .oobNan → d.format.floating = true) ∧
  d.box.traversal 0 = 1

instance validDecidable {outer : Nat} (d : Descriptor outer) : Decidable (Valid d) := by
  unfold Valid
  infer_instance

/-- The transfer box of a `.tile::gather4` load: the map's box (whose dimension 1 is one) with
four rows of unit traversal (EXT-TMA-GATHER4). -/
def Descriptor.fourRows {outer : Nat} (d : Descriptor outer) : Descriptor outer :=
  { d with box := ⟨fun axis => if axis.val = 1 then 4 else d.box.size axis,
                   fun axis => if axis.val = 1 then 1 else d.box.traversal axis⟩ }

/-- The bounding box's global start is 16-byte aligned (§5.5.3.1). Base and outer strides are
multiples of 16 (`Valid`), so this is the innermost coordinate's byte offset (EXT-TMA-BOX-ALIGN). -/
def BoxAligned {outer : Nat} (d : Descriptor outer) (origin : Fin (outer + 1) → Int) : Prop :=
  origin 0 * d.format.bytes % 16 = 0

instance boxAlignedDecidable {outer : Nat} (d : Descriptor outer) (origin : Fin (outer + 1) → Int) :
    Decidable (BoxAligned d origin) := by
  unfold BoxAligned
  infer_instance

end PTX.TensorDescriptor
