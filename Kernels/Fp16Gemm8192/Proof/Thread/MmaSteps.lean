-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.Simple
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_full
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_mma
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_commit
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_clcWait
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_clcLoad
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_clcStatus
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_clcFirst
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_clcFence
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_accCommit
public import Kernels.Fp16Gemm8192.Proof.Thread.MmaSteps.step_elect

@[expose] public section

/-! # The MMA warps' events

The election, the CLC response (poll, read, queries, fence, acknowledgement), the
accumulator poll and commit, and the K loop of thirty-two trips over four slots (each slot
polls its full barrier, issues four MMAs and commits to its empty barrier). Each event
continues at the next instruction; the local code between events is evaluated by segments. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000



end
end PTX.Kernels.Fp16Gemm8192.Proof.Mma
