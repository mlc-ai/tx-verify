-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Lemmas.Tensor.TensorTile

@[expose] public section

namespace PTX.TensorDescriptor

theorem format_bytes_pos (f : Format) : 0 < f.bytes := by cases f <;> decide

theorem effective_step_pos {outer : Nat} {d : Descriptor outer} (h : Valid d)
    (axis : Fin (outer + 1)) : 0 < TensorTile.step d.box axis := by
  unfold TensorTile.step
  split
  · decide
  · exact (h.2.2.2.2.2.1 axis).1

/-- The selected count cannot exceed the box extent for any positive traversal. -/
theorem count_le_box {outer : Nat} {d : Descriptor outer} (h : Valid d)
    (axis : Fin (outer + 1)) : TensorTile.count d.box axis ≤ d.box.size axis := by
  have hp := effective_step_pos h axis
  by_contra hn
  have hi : d.box.size axis < TensorTile.count d.box axis := by omega
  have hh := (TensorTile.index_lt_count_iff d.box axis hp (d.box.size axis)).mp hi
  have hm : d.box.size axis ≤ d.box.size axis * TensorTile.step d.box axis := by
    simpa using Nat.mul_le_mul_left (d.box.size axis) hp
  omega

end PTX.TensorDescriptor
