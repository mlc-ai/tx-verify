-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec
public import Kernels.Fp16Gemm8192.Ptx
public import Tactics.KernelRfl
public import Core.Source.Decode
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section

/-! The frozen production PTX decodes to the exact 1097-instruction program used by the
specification, certified by one kernel reduction of the Core decoder. -/
namespace PTX.Kernels.Fp16Gemm8192

set_option maxRecDepth 100000 in
theorem decode_eq : Decode.kernelIn Generated.Fp16Gemm8192.module.globals
    Generated.Fp16Gemm8192.gemm_kernel = .ok kernel := by
  kernel_rfl

end PTX.Kernels.Fp16Gemm8192
