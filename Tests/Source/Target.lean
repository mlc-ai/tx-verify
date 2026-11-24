-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Kernels.BlockSum.Ptx
public import Kernels.CopyDynamic.Ptx
public import Kernels.CopyLdg.Ptx
public import Kernels.RmsNorm.Ptx
public import Kernels.RowSum.Ptx
public import Kernels.TmaCopy.Ptx
public import Kernels.TcGemm.Ptx
public import Kernels.Fp16Gemm8192.Ptx
public import Kernels.AddOne.Ptx

/-! # Module targets (PROG-DECODE)

Every proved kernel's module targets `sm_70` or later, so the decoder's sm_70 convergence
rules apply; a module for `sm_60`, or without a `.target`, is rejected. -/

namespace PTX.Tests.Target
open PTX.Syntax

example : Decode.target Generated.BlockSum.module.directives = .ok () := by rfl
example : Decode.target Generated.CopyDynamic.module.directives = .ok () := by rfl
example : Decode.target Generated.CopyLdg.module.directives = .ok () := by rfl
example : Decode.target Generated.RmsNorm.module.directives = .ok () := by rfl
example : Decode.target Generated.RowSum.module.directives = .ok () := by rfl
example : Decode.target Generated.TmaCopy.module.directives = .ok () := by rfl
example : Decode.target Generated.TcGemm.module.directives = .ok () := by rfl
example : Decode.target Generated.Fp16Gemm8192.module.directives = .ok () := by rfl
example : Decode.target Generated.AddOne.module.directives = .ok () := by rfl

example : (Decode.target [[".version", "9.2"], [".target", "sm_60"]]).toBool = false := by rfl
example : (Decode.target [[".version", "9.2"], [".target", "sm_61", ",", "debug"]]).toBool =
    false := by
  rfl
example : (Decode.target [[".version", "9.2"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70"]]).toBool = true := by rfl
example : (Decode.target [[".target", "sm_70junk"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70", ",", "sm_80"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70", "sm_80"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70", ",", "bogus"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70", ","]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70", ",", "debug"]]).toBool = true := by rfl
example : (Decode.target [[".target", "sm_100a", ",", "texmode_unified"]]).toBool = true := by rfl
-- `map_f64_to_f32` maps every double-precision instruction to single precision (§11.1.2); the
-- model executes `.f64` instructions in double precision, so the option is rejected.
example : (Decode.target [[".target", "sm_70", ",", "map_f64_to_f32"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_100a", ",", "debug", ",", "map_f64_to_f32"]]).toBool =
    false := by
  rfl
example : (Decode.target [[".target", "compute_100"]]).toBool = true := by rfl
example : (Decode.target [[".target", "compute_61"]]).toBool = false := by rfl
example : (Decode.target [[".target", "compute_100junk"]]).toBool = false := by rfl
example : (Decode.target [[".target", "debug"]]).toBool = false := by rfl
example : (Decode.target [[".target", "sm_70"], [".target", "sm_80"]]).toBool = false := by rfl

end PTX.Tests.Target
