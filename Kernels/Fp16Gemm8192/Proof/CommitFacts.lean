-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.MemoryPeer
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.CommitCover
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.PeerReads
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Exit
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The commit branch of `Unsafe`, and the shared memory lifetimes

This file sits at the top of the proof tree, outside the layer order (as `TensorFacts.lean` does):
it supplies the safety layer's commit branch (`Safety.no_commit_unsafe`) with the thread facts, and
its shared memory lifetime branch (`Safety.Memory.no_sharedLifetimeUnsafe`) with the protocols'
exports, all from the thread facts (`threadFacts`) and the CLC readers' values
(`ClcRing.readerValues`, over the region layer's response writers): the commits' notifications
(`commitNotified`), the exit order and the exit protocol (`exitOrder`, `ClcRing.exitNotified`), the
input ring's exit coverage (`InputRing.tensorExitFinished`), the MMAs' completions
(`InputRing.mmaExitDone`) and their operand reads (`InputRing.readsFinished`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every commit notified an exited CTA it targets, from the thread facts. -/
theorem commit_notified (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    CommitNotified L X :=
  have ht := threadFacts hpre hX
  commitNotified hpre hX ht (ClcRing.allResponsesAgree hpre hX ht
    (Region.responseWriters hpre hX ht))

/-- **No commit is unsafe.** -/
theorem no_tcCommitUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ TcCommitUnsafe L X :=
  Safety.no_commit_unsafe hpre hX (threadFacts hpre hX)

/-- **No shared memory use is unsafe.** -/
theorem no_sharedLifetimeUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ SharedLifetimeUnsafe L kernel Prod X :=
  have ht := threadFacts hpre hX
  have hrw := Region.responseWriters hpre hX ht
  have hcn := commit_notified hpre hX
  Safety.Memory.no_sharedLifetimeUnsafe hpre hX ht (exitOrder hpre hX ht)
    (ClcRing.exitNotified hpre hX ht (ClcRing.readerValues hpre hX ht hrw)) hcn
    (InputRing.tensorExitFinished hpre hX ht (ClcRing.allResponsesAgree hpre hX ht hrw))
    (InputRing.mmaExitDone hpre hX ht hcn) (InputRing.readsFinished hpre hX ht hcn)

end

end PTX.Kernels.Fp16Gemm8192.Proof
