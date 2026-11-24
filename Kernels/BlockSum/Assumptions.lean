-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal

@[expose] public section

/-!
# The assumptions of `block_sum`

The theorems of `Theorem.lean` assume exactly `idealAdd`, and nothing else.
-/

namespace PTX.Kernels.BlockSum.Assumptions
open PTX

/-- The kernel's only floating instruction, the reduction's `add.f32` (§9.7.3.3), is read as
exact real addition, so that the result is the exact real sum of the CTA's inputs. -/
noncomputable def idealAdd : Assumption :=
  Assumption.idealReal "block-sum-ideal-add" { float := [.add .f32] }
    "block_sum combines partial sums with its one add.f32; PTX rounds every sum (\".rn \
    mantissa LSB rounds to nearest even\"), while the theorem states the exact real CTA sum."

end PTX.Kernels.BlockSum.Assumptions
