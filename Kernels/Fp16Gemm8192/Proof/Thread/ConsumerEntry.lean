-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.Simple
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcWait
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcLoad
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcStatus
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.lead_lt
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcFirst
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcFence
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.tile_seg
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEntry.step_clcBar

@[expose] public section

/-! # The consumer warps' step lemmas

Each lemma takes the consumer's abstract state `d` at its site, the instruction there and the
event that fires, and gives the successor of `next` with its concrete state: the local steps
between the event and the next site are evaluated by `cons_seg`, the branches are split with
`run_bra`, and the address arithmetic is closed by bounded lemmas. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000



end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
