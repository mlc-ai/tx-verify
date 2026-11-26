-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Where an unswizzled box writes

A proof tool. A tensor box without swizzle places slot `(x, y, byte)` at
`base + y * (c * n) + x * n + byte` (`c` the columns, `n` the element bytes), so every slot of a
box of `R` rows lies in the `R * (c * n)` bytes after the shared base, in the base's space and CTA
(`box_none_sharedLoc`); for a tensor load's written byte, `writeLoc_none`. -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- **An unswizzled box's slot lies in the rows after its shared base.** -/
theorem box_none_sharedLoc (b : TensorBox) (hsw : b.descriptor.swizzle = .none)
    (slot : TensorTransfer.Slot b.descriptor) :
    (b.sharedLoc slot).space = b.sharedBase.space ∧ (b.sharedLoc slot).cta = b.sharedBase.cta ∧
      b.sharedBase.addr ≤ (b.sharedLoc slot).addr ∧
      (b.sharedLoc slot).addr < b.sharedBase.addr + TensorTile.rows b.descriptor.box *
        (TensorTile.count b.descriptor.box 0 * b.descriptor.format.bytes) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨k, hk⟩⟩ := slot
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes, hsw, TensorTile.swizzleWidth, TensorSwizzle.offset_none]
  refine ⟨trivial, trivial, by omega, ?_⟩
  set c := TensorTile.count b.descriptor.box 0
  set n := b.descriptor.format.bytes
  set R := TensorTile.rows b.descriptor.box
  have h1 : x * n + k < c * n := by
    have := Nat.mul_le_mul_right n (show x + 1 ≤ c by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have h2 : y * max (c * n) 0 + c * n ≤ R * (c * n) := by
    have := Nat.mul_le_mul_right (c * n) (show y + 1 ≤ R by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [Nat.max_zero]
    omega
  omega

/-- **An unswizzled load writes the rows after its shared base.** -/
theorem writeLoc_none {s : Spec} {x y k : Nat} {l : Loc} (hsw : s.descriptor.swizzle = .none)
    (h : writeLoc s x y k = some l) :
    l.space = s.sharedBase.space ∧ l.cta = s.sharedBase.cta ∧ s.sharedBase.addr ≤ l.addr ∧
      l.addr < s.sharedBase.addr + TensorTile.rows s.descriptor.box *
        (TensorTile.count s.descriptor.box 0 * s.descriptor.format.bytes) := by
  unfold writeLoc at h
  obtain ⟨slot, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact box_none_sharedLoc s.toTensorBox hsw slot

end PTX.TensorCopy
