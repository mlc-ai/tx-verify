-- SPDX-License-Identifier: Apache-2.0
module

public meta import Core.Source.Decode
public meta import Kernels.Fp16Gemm8192.Ptx

/-! Decode the unmodified frozen production program with its actual declarations.
This executable coverage check is not a kernel correctness theorem. -/
open PTX
#eval show IO Unit from do
  match Decode.kernelIn Generated.Fp16Gemm8192.module.globals
      Generated.Fp16Gemm8192.gemm_kernel with
  | .ok k => IO.println s!"production decode: {k.code.length} instructions"
  | .error e => throw (IO.userError s!"production decode failed: {e}")
