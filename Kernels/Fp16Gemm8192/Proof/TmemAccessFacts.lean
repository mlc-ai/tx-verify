-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TmemAccess
public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrResult
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.ExitDone
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemAlloc.BaseValue
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The Tensor Memory access branch of `Unsafe`

This file sits at the top of the proof tree, outside the layer order (as `TensorFacts.lean` does):
it supplies the safety layer's Tensor Memory access branch (`Safety.no_access_unsafe`) with the
accumulator ring's completion before the release
(`TmemRing.tmemExitDone`), from the thread facts (`threadFacts`) and the CLC readers' agreement
(`ClcRing.allResponsesAgree`, over the region layer's response writers). The same completion gives
the MMA instruction branch its accumulators' lifetimes (`mmaReleased`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

/-- **Every release of an MMA's accumulator follows the MMA's completion.** -/
theorem mmaReleased {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : Safety.MmaReleased L X :=
  have ht := threadFacts hpre hX
  Safety.mma_released hpre hX ht (TmemRing.tmemExitDone hpre hX ht
    (ClcRing.allResponsesAgree hpre hX ht (Region.responseWriters hpre hX ht)))

/-- **No Tensor Memory access is unallocated or outlives its allocation.** -/
theorem no_tmemAccessUnsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ Tmem.Pair.AccessUnsafe L X :=
  have ht := threadFacts hpre hX
  Safety.no_access_unsafe hpre hX ht
    (TmemRing.tmemExitDone hpre hX ht
      (ClcRing.allResponsesAgree hpre hX ht (Region.responseWriters hpre hX ht)))

end

end PTX.Kernels.Fp16Gemm8192.Proof
