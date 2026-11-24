-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorTransfer
public import Core.Async.Tensor.TensorCopy

namespace PTX.TensorTransfer

/-- A slot's global source and shared byte. -/
private def place {outer : Nat} (d : TensorDescriptor.Descriptor outer) (origin : Fin (outer + 1) →
    Int)
    (rows : Option (Fin 4 → Int)) (base : Nat) (slot : TensorTransfer.Slot d) :
    Option Nat × Nat :=
  ((⟨outer, d, origin, ⟨.shared, 0, base⟩, rows⟩ : TensorBox).globalAddress slot,
    TensorTile.sharedByte d.box d.format.bytes d.swizzle base slot.1.val slot.2.1.val slot.2.2.val)
private def tile : TensorDescriptor.Descriptor 1 :=
  ⟨.f16, 4096, ![8, 2], ![16], ⟨![8, 2], ![1, 1]⟩, .b128, .zero, .small⟩
private def lastByte : Slot tile := ⟨⟨7, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩
example : bytes tile = 32 := rfl
-- Padding occupies shared addresses but is not counted as transferred data.
example : TensorTile.rowBytes tile.box tile.format.bytes tile.swizzle = 128 := rfl
example : place tile ![0, 0] none 0 lastByte = ⟨some 4127, 159⟩ := by decide
example : place tile ![0, 1] none 0 lastByte = ⟨none, 159⟩ := by decide
example : place tile ![0, 0] none 128 lastByte = ⟨some 4127, 303⟩ := by decide

end PTX.TensorTransfer
