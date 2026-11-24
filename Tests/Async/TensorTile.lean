-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorTile

namespace PTX.TensorTile

private def elements {rank : Nat} (b : Box rank) : Nat :=
  Finset.univ.prod (count b)
private def box : Box 2 := ⟨![8, 7], ![8, 3]⟩
private def tensor : TensorAddress.Geometry 2 := ⟨1024, 2, ![16, 8], ![2, 32]⟩
-- Seven positions with step three select offsets 0, 3, 6, not seven elements.
example : count box 0 = 8 := rfl
example : count box 1 = 3 := rfl
example : elements box = 24 := by decide
example : coord box ![2, 1] ![4, 2] = ![6, 7] := by decide
example : source tensor box ![2, 1] ![4, 2] 1 = some (some 1261) := by decide
-- Selected OOB element, unlike a position not selected by this tile.
example : source tensor box ![2, 2] ![4, 2] 0 = some none := by decide
example : source tensor box ![2, 1] ![4, 3] 0 = none := by decide
example : source tensor box ![-3, 1] ![0, 0] 0 = some none := by decide

-- A 16-byte inner row occupies a full 128-byte row under 128B swizzle.
example : rowBytes box 2 .b128 = 128 := rfl
example : sharedByte box 2 .b128 0 0 1 0 = 144 := rfl
example : sharedByte box 2 .b128 128 0 0 0 = 144 := rfl
example : sharedByte box 2 .none 128 0 1 0 = 144 := rfl

end PTX.TensorTile
