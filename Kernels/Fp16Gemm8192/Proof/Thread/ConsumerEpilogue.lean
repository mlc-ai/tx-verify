-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Simple
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.step_commit_7
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.step_barB
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.step_tma
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.step_fence

@[expose] public section

/-! # The consumer's epilogue: slices, the exit and the Tensor Memory release

Each slice of a tile: the group waits for the previous TMA store to release the staging
buffer, synchronizes, stores four vectors, synchronizes, and on the group's first thread
fences, issues the TMA store and commits it. After the last slice the thread takes the next
task or drains its stores and meets the cluster; warp 0 releases Tensor Memory and reads the
base address back, and every thread leaves.

These are the step lemmas of those states. A four-element vector store is four write events of
one instruction: its sub-aware state `AtS` carries the element, and `step_store` continues
through the four elements to the next store or the barrier after the slice's stores. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000



end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
