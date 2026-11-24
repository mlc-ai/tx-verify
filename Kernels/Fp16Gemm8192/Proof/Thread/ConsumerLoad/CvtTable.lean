-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtCheck0
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtCheck1
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtCheck2
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.CvtCheck3

@[expose] public section

/-! The table facts of every load's conversions. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer

theorem cvtCheck_all (j : Fin 16) : cvtCheck j = true := by
  by_cases h0 : j.val < 4
  · exact cvtCheck_q0 j h0
  by_cases h1 : j.val < 8
  · exact cvtCheck_q1 j (by omega) h1
  by_cases h2 : j.val < 12
  · exact cvtCheck_q2 j (by omega) h2
  exact cvtCheck_q3 j (by omega)

theorem cvtTable (j : Fin 16) : CvtTable j := .of_check (cvtCheck_all j)

end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
