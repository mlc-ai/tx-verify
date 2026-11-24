-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PTX.TensorAddress

/-! ## THREAD-TENSOR-GLOBAL-ADDRESS — global tensor coordinates and byte addresses
Statement: The global address of a byte of an element is the tensor base address plus, over the
  axes, the coordinate times the byte stride, plus the byte's position within the element. A
  coordinate that is negative or reaches the extent on any axis has no global address.

Defs: TensorAddress.Geometry, TensorAddress.InBounds, TensorAddress.byteAddress,
  TensorAddress.lookup

Source:
- §5.5.1 (dimensions and tensor strides)
- §5.5.3.1 (bounding-box origin)
- §5.5.3.3 (out-of-boundary access)
- EXT-TMA-GEOMETRY (the address formula)

Direction: reading

Applies: Byte-sized, non-interleaved tensor elements, with dimensions ordered fastest first

Premises: The descriptor supplies the tensor geometry. Instruction legality, descriptor encoding,
  traversal selection and address-space allocation are checked separately.

Effect: Global address calculation only. The geometry is rank-polymorphic; the consuming ISA
  operation must check rank 1..5, positive extents, element type, stride alignment/ranges and
  stride[0] = elementBytes. In particular, returning none is not permission to access an invalid
  descriptor.
-/
/-- The geometry of a global tensor of `rank` axes, fastest first: its base address, the byte size
of an element, and for each axis the extent in elements and the stride in bytes. -/
structure Geometry (rank : Nat) where
  base : Nat
  elementBytes : Nat
  extent : Fin rank → Nat
  stride : Fin rank → Nat

/-- The coordinate lies inside the tensor: on every axis it is nonnegative and below the extent. -/
def InBounds {rank : Nat} (d : Geometry rank) (coord : Fin rank → Int) : Prop :=
  ∀ axis, 0 ≤ coord axis ∧ coord axis < (d.extent axis : Int)

/-- The global address of byte `byte` of the element at `coord`: the base plus the sum over the axes
of the coordinate times the stride, plus `byte`. -/
def byteAddress {rank : Nat} (d : Geometry rank) (coord : Fin rank → Int)
    (byte : Nat) : Nat :=
  d.base + (Finset.univ.sum fun axis => (coord axis).toNat * d.stride axis) + byte

/-- A global source exists only for an in-range element and a byte of that element. -/
def lookup {rank : Nat} (d : Geometry rank) (coord : Fin rank → Int)
    (byte : Nat) : Option Nat :=
  if (∀ axis, 0 ≤ coord axis ∧ coord axis < (d.extent axis : Int)) ∧
      byte < d.elementBytes then some (byteAddress d coord byte) else none

end PTX.TensorAddress
