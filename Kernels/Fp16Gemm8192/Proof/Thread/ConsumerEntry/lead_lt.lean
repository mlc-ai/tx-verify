-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base

@[expose] public section

/-! One step of `ConsumerEntry`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem lead_lt (tid : Nat) : tid / 32 % 4 ||| tid % 32 < 2 ^ 32 :=
  Nat.or_lt_two_pow (by omega) (by omega)

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
