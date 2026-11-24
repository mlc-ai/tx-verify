-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal

@[expose] public section

/-!
# The assumptions of `row_sum`

The theorems of `Theorem.lean` assume exactly `idealAdd`, and nothing else.
-/

namespace PTX.Kernels.RowSum.Assumptions
open PTX

/-- The kernel's only floating instruction, the loop's `add.f32` (§9.7.3.3), is read as exact
real addition, so that `B[r]` is the exact real sum of row `r`. -/
noncomputable def idealAdd : Assumption :=
  Assumption.idealReal "row-sum-ideal-add" { float := [.add .f32] }
    "row_sum accumulates each row with its one add.f32; PTX rounds every sum (\".rn mantissa \
    LSB rounds to nearest even\"), while the theorem states the exact real row sum."

end PTX.Kernels.RowSum.Assumptions
