-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorSwizzle

namespace PTX.TensorSwizzle

-- Rows from the documented 16-byte chunk permutations.
example : (List.range 8).map (fun c => offset .b128 0 (128 + 16 * c)) =
    [144, 128, 176, 160, 208, 192, 240, 224] := by decide
example : (List.range 8).map (fun c => offset .b64 0 (256 + 16 * c)) =
    [288, 304, 256, 272, 352, 368, 320, 336] := by decide
example : (List.range 8).map (fun c => offset .b32 0 (128 + 16 * c)) =
    [144, 128, 176, 160, 208, 192, 240, 224] := by decide
-- A 128-byte-aligned base need not be aligned to the whole repeating pattern.
example : offset .b128 128 0 = 16 := rfl
example : offset .b128 128 15 = 31 := rfl
example : offset .b128 1024 0 = 0 := rfl
example : offset .b64 512 0 = 0 := rfl
example : offset .b32 256 0 = 0 := rfl
example : offset .none 128 243 = 243 := rfl

-- No address collision, for arbitrary offsets and base phases.
example (mode : Mode) (base a b : Nat) (h : a ≠ b) :
    offset mode base a ≠ offset mode base b := fun heq =>
  h (offset_injective mode base heq)

end PTX.TensorSwizzle
