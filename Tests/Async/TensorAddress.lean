-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.Fin.VecNotation
public import Lemmas.Tensor.TensorAddress

namespace PTX.TensorAddress

-- Row padding is represented by the stride, not by changing the extent.
private def padded : Geometry 2 :=
  ⟨4096, 2, ![64, 8], ![2, 160]⟩
example : lookup padded ![3, 2] 1 = some 4423 := by decide
example : lookup padded ![-1, 2] 0 = none := by decide
example : lookup padded ![64, 2] 0 = none := by decide
example : lookup padded ![3, 8] 0 = none := by decide
example : lookup padded ![3, 2] 2 = none := by decide
-- The outer stride can describe a split inner dimension, as in a 3D tensor map.
private def splitK : Geometry 3 :=
  ⟨0, 2, ![64, 8192, 128], ![2, 16384, 128]⟩
example : lookup splitK ![7, 3, 2] 0 = some 49422 := by decide

end PTX.TensorAddress
