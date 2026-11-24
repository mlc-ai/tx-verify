-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorDescriptor

namespace PTX.TensorDescriptor

private def tile : Descriptor 1 :=
  ⟨.f16, 4096, ![8192, 8192], ![16384], ⟨![64, 128], ![1, 1]⟩, .b128, .zero, .small⟩
example : Valid tile := by decide
example : ¬ Valid { tile with base := 4097 } := by decide
example : ¬ Valid { tile with box := ⟨![65, 128], ![1, 1]⟩ } := by decide
example : ¬ Valid { tile with box := ⟨![128, 128], ![1, 1]⟩ } := by decide
example : ¬ Valid { tile with box := ⟨![64, 0], ![1, 1]⟩ } := by decide
example : ¬ Valid { tile with box := ⟨![64, 128], ![1, 0]⟩ } := by decide
example : ¬ Valid { tile with format := .u16, fill := .oobNan } := by decide
example : Valid { tile with fill := .oobNan } := by decide
-- §5.5.3.2: a non-interleaved map's dimension-0 traversal stride must be 1.
example : ¬ Valid { tile with box := ⟨![64, 128], ![2, 2]⟩ } := by decide
example : Valid { tile with box := ⟨![64, 128], ![1, 2]⟩ } := by decide
-- Non-monotonic byte strides are needed for a split inner dimension.
private def splitK : Descriptor 2 :=
  ⟨.bf16, 4096, ![64, 8192, 128], ![16384, 128],
    ⟨![64, 128, 2], ![1, 1, 1]⟩, .b128, .zero, .small⟩
example : Valid splitK := by decide
example : (geometry splitK).stride 0 = 2 := rfl
example : (geometry splitK).stride 1 = 16384 := rfl
example : (geometry splitK).stride 2 = 128 := rfl

end PTX.TensorDescriptor
