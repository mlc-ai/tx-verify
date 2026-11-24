-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Cvt

@[expose] public section

/-! The table facts of the conversions of loads 8 to 11, checked by evaluation (a
quarter of the loads per module, so that the checks run in parallel). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer

theorem cvtCheck_q2 : ∀ j : Fin 16, 8 ≤ j.val → j.val < 12 → cvtCheck j = true := by decide +kernel

end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
