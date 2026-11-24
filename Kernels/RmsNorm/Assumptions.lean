-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Assumption.ApproxExact

@[expose] public section

/-!
# The assumptions of `rmsnorm`

The theorems of `Theorem.lean` assume exactly `idealArith` and `exactApprox`, and nothing else.
-/

namespace PTX.Kernels.RmsNorm.Assumptions
open PTX

/-- The kernel's rounded floating instructions — `add.ftz.f32`, `fma.rn.ftz.f32`,
`mul.rz.ftz.f32x2`, `cvt.f32.f16` and `cvt.rn.f16x2.f32` (§9.7.3.3, §9.7.3.6, §9.7.3.5,
§9.7.10.25) — are read as exact real arithmetic, so that the output is the exact real RMS
normalization. -/
noncomputable def idealArith : Assumption :=
  Assumption.idealReal "rmsnorm-ideal-arith"
    { float := [.add .f32, .fma .f32, .mulF32x2, .cvtF32F16, .cvtRnF16x2F32] }
    "rmsnorm computes the sum of squares, the scaling and the conversions to and from f16 with \
    exactly these forms; PTX rounds their results (\".rn mantissa LSB rounds to nearest \
    even\"), while the theorem states the exact real RMS normalization."

/-- The kernel's one `div.approx.ftz.f32` and one `rsqrt.approx.ftz.f32` (§9.7.3.8, §9.7.3.16)
are read as the exact `a / b` and `1 / sqrt a`. -/
noncomputable def exactApprox : Assumption :=
  Assumption.approxExact "rmsnorm-exact-approx" [.div .f32, .rsqrt .f32]
    "rmsnorm computes the mean with one div.approx.ftz.f32 and the inverse root with one \
    rsqrt.approx.ftz.f32; PTX gives only approximations (\"div.approx.f32 implements a fast \
    approximation to divide, computed as d = a * (1/b)\", \"rsqrt.approx implements an \
    approximation to the reciprocal square root.\"), while the theorem states the exact \
    real result."

end PTX.Kernels.RmsNorm.Assumptions
