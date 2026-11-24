-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorCopy

@[expose] public section

/-! # A slot a tensor load reads is in its box

The read side of `writeLoc_bounds`: a slot whose source location a tensor load reads is a slot of
its box (`readLoc_bounds`). -/

namespace PTX.TensorCopy
open TensorDescriptor

/-- A slot a tensor load reads is in its box. -/
theorem readLoc_bounds {s : Spec} {x y byte : Nat} {l : Loc} (h : readLoc s x y byte = some l) :
    x < TensorTile.count s.descriptor.box 0 ∧ y < TensorTile.rows s.descriptor.box ∧
      byte < s.descriptor.format.bytes := by
  rw [readLoc_source] at h
  unfold TensorTransfer.slotAt at h
  by_cases hx : x < TensorTile.count s.descriptor.box 0
  · by_cases hy : y < TensorTile.rows s.descriptor.box
    · by_cases hb : byte < s.descriptor.format.bytes
      · exact ⟨hx, hy, hb⟩
      · simp [hx, hy, hb] at h
    · simp [hx, hy] at h
  · simp [hx] at h

end PTX.TensorCopy
