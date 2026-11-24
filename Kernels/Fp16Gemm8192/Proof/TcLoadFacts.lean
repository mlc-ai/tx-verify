-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcLoads
public import Kernels.Fp16Gemm8192.Proof.TcInstrFacts
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.ExitDone
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemAlloc.BaseValue
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The Tensor Memory loads' branch of `Unsafe`, and the undefined-behaviour branch

This file sits at the top of the proof tree, outside the layer order (as `TensorFacts.lean` does):
it supplies the accumulator ring's load sources (`TmemRing.loadSources`), from the thread facts, the
MMAs' completed values (`no_instructionUnsafe`) and the Tensor Memory accesses' lifetimes
(`tmem_live`, from the accumulator ring's completion before the release); with them the loaded
words (`Safety.loadWords_of`) and the undefined-behaviour branch (`Safety.no_ub`, with the CLC
readers' values and the base word). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every Tensor Memory access is allocated and done before the releases of its covering
allocations** (`TmemLive`). -/
theorem tmem_live (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : TmemLive L X :=
  have ht := threadFacts hpre hX
  Safety.tmem_live hpre hX ht
    (TmemRing.tmemExitDone hpre hX ht
      (ClcRing.allResponsesAgree hpre hX ht (Region.responseWriters hpre hX ht)))

/-- **Every required Tensor Memory read has a source** (`TcMma.SourceSafe`): a load register by
the accumulator ring (`TmemRing.loadSources`), an MMA's accumulator and A reads by the MMAs'
results (`Safety.mma_sources`). -/
theorem tc_supported (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    TcMma.SourceSafe L Prod X :=
  have ht := threadFacts hpre hX
  have hm := Safety.mma_sources hpre hX ht
    (InputRing.operandCopies hpre hX ht (Region.inputAccessors hpre hX ht)) (mmaReleased hpre hX)
  TcMma.sourceSafe_iff.mpr ⟨TmemRing.loadSources hpre hX ht
    (Classical.not_not.mp (no_instructionUnsafe hpre hX)) (tmem_live hpre hX), hm.1, hm.2⟩

/-- **Every word a Tensor Memory load returns is a single-precision float** (`LoadWords`). -/
theorem load_words (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : LoadWords X :=
  Safety.loadWords_of hX (TmemRing.tmemWords hX (threadFacts hpre hX)) (tc_supported hpre hX)

/-- **No event is undefined behaviour.** -/
theorem no_ub (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : ¬ HasUb X :=
  have ht := threadFacts hpre hX
  Safety.no_ub hX ht (ClcRing.readerValues hpre hX ht (Region.responseWriters hpre hX ht))
    (Safety.baseWord_of_value (TmemAlloc.baseValue hpre hX ht)) (load_words hpre hX)

end

end PTX.Kernels.Fp16Gemm8192.Proof
