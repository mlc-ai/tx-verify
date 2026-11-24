-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorTile
public import Mathlib.Data.Fin.VecNotation

/-! Tile geometry of the production GEMM's tensor maps (THREAD-TENSOR-TILE): operand boxes of
64 x 128 FP16 with 128-byte swizzle, output boxes of 32 x 128 FP16 with 64-byte swizzle,
over 8192 x 8192 row-major matrices. -/
namespace PTX.Tests.TensorTileProduction
open TensorTile

private def elements {rank : Nat} (b : Box rank) : Nat :=
  Finset.univ.prod (count b)

private def boxA : Box 2 := ⟨![64, 128], ![1, 1]⟩
private def boxD : Box 2 := ⟨![32, 128], ![1, 1]⟩
private def matrix : TensorAddress.Geometry 2 := ⟨4096, 2, ![8192, 8192], ![2, 16384]⟩

-- A box row is exactly one 128-byte swizzle row; 8192 elements per box.
example : rowBytes boxA 2 .b128 = 128 := rfl
example : elements boxA = 8192 := by decide
-- The 64-byte-swizzled output row is 64 bytes.
example : rowBytes boxD 2 .b64 = 64 := rfl

-- Column 0 of the first eight rows walks the 16-byte chunk diagonal (row r -> chunk r).
example : (List.range 8).map (fun r => sharedByte boxA 2 .b128 1024 0 r 0) =
    [1024, 1168, 1312, 1456, 1600, 1744, 1888, 2032] := by decide
-- Interior and last element of a stage at 1024, and the start of the next stage at 17408.
example : sharedByte boxA 2 .b128 1024 8 3 1 = 1441 := by decide
example : sharedByte boxA 2 .b128 1024 63 127 1 = 17295 := by decide
example : sharedByte boxA 2 .b128 17408 0 0 0 = 17408 := by decide
-- The output staging tile uses the 64-byte pattern.
example : sharedByte boxD 2 .b64 197632 5 9 0 = 198218 := by decide

-- Global sources: the last element of the matrix, and zero fill past the boundary.
example : source matrix boxA ![8128, 8100] ![63, 91] 1 = some (some 134221823) := by decide
example : source matrix boxA ![8128, 8100] ![63, 92] 1 = some none := by decide
-- Indices outside the box, or a third byte of an FP16 element, are not selected.
example : source matrix boxA ![8128, 8100] ![64, 0] 0 = none := by decide
example : source matrix boxA ![0, 0] ![0, 0] 2 = none := by decide
-- Negative origins are partially out of bounds rather than wrapped.
example : source matrix boxA ![-8, 0] ![7, 0] 0 = some none := by decide
example : source matrix boxA ![-8, 0] ![8, 0] 0 = some (some 4096) := by decide

end PTX.Tests.TensorTileProduction
