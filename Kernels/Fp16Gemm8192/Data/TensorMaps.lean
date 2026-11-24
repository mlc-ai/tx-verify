-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor

@[expose] public section

/-! Tensor maps of the production FP16 GEMM, as the host encodes them.

The PTX receives each map as an opaque 128-byte `.param`. Its contents come from the
host's `cuTensorMapEncodeTiled` calls in TIRx `prepare_host`. `manifest.json` records the
exact arguments of the three calls, captured from the production host code at run time
(`gen_ptx.py --tensor-maps`); `validate.py` checks that they match the definitions below
and, on a GPU, that the bytes the production host passes are exactly the bytes an
independent `cuTensorMapEncodeTiled` call with these arguments produces. The driver's
documented encoding semantics is the remaining trust (EXT-LAUNCH). L2 promotion is a
cache hint with no memory-model effect. The allocation class is a device attribute of
the global allocation, not an encoding argument, so it stays a parameter. -/
namespace PTX.Kernels.Fp16Gemm8192
open TensorDescriptor

/-- A rank-2, non-interleaved tiled map: inner extent, outer extent, outer row stride in
bytes, inner and outer box sizes, unit element strides and zero OOB fill. -/
def encodeTiled (format : Format) (base inner outer stride boxInner boxOuter : Nat)
    (swizzle : TensorSwizzle.Mode) (cls : AllocationClass) : Descriptor 1 where
  format := format
  base := base
  extent := fun i => if i.val = 0 then inner else outer
  outerStride := fun _ => stride
  box := ⟨fun i => if i.val = 0 then boxInner else boxOuter, fun _ => 1⟩
  swizzle := swizzle
  fill := .zero
  allocationClass := cls

/-- `A` (M x K, K contiguous): 64-element K boxes of 128 rows, 128-byte swizzle. -/
def mapA (base : Nat) (cls : AllocationClass) : Descriptor 1 :=
  encodeTiled .f16 base 8192 8192 16384 64 128 .b128 cls
/-- `B` (N x K, K contiguous): encoded like `A`. -/
def mapB (base : Nat) (cls : AllocationClass) : Descriptor 1 :=
  encodeTiled .f16 base 8192 8192 16384 64 128 .b128 cls
/-- `D` (M x N, N contiguous): 32-element epilogue boxes of 128 rows, 64-byte swizzle. -/
def mapD (base : Nat) (cls : AllocationClass) : Descriptor 1 :=
  encodeTiled .f16 base 8192 8192 16384 32 128 .b64 cls

theorem mapA_valid {base : Nat} {cls : AllocationClass} (h : base % 16 = 0) :
    Valid (mapA base cls) := by
  refine ⟨by decide, h, ?_⟩
  simp only [mapA, encodeTiled]
  refine ⟨fun i => ?_, fun _ => by decide, fun i => ?_, fun _ => by decide, by decide,
    .inr (by decide), fun h => (by cases h), (by decide)⟩ <;> split <;> decide

theorem mapB_valid {base : Nat} {cls : AllocationClass} (h : base % 16 = 0) :
    Valid (mapB base cls) := mapA_valid h

theorem mapD_valid {base : Nat} {cls : AllocationClass} (h : base % 16 = 0) :
    Valid (mapD base cls) := by
  refine ⟨by decide, h, ?_⟩
  simp only [mapD, encodeTiled]
  refine ⟨fun i => ?_, fun _ => by decide, fun i => ?_, fun _ => by decide, by decide,
    .inr (by decide), fun h => (by cases h), (by decide)⟩ <;> split <;> decide

end PTX.Kernels.Fp16Gemm8192
