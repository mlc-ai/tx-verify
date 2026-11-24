-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Async
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Loads
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts
public import Kernels.Fp16Gemm8192.Proof.GuardFacts

@[expose] public section

/-! # The MMA and tensor-load obligations of a maximal execution

This file sits at the top of the proof tree, outside the layer order (as `ProgressFacts.lean` does):
it supplies the progress layer's `mma_steps` with the input ring's operand sources
(`InputRing.operandSources`), from the thread facts and the input stages' accessors
(`Region.inputAccessors`),
and `tensor_steps` with the tensor loads' fixed global sources (`InputRing.tensorSources`), from the
thread facts alone. So a maximal execution has no open MMA obligation (`mma_obl`) and no open
tensor-load obligation (`tensor_obl`): the `mmaObl` and `tensorObl` classes of
`Progress.ClassFacts`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **A maximal execution has completed every MMA.** -/
theorem mma_obl (hpre : Pre P L mem0) :
    ∀ X, Maximal L kernel Prod mem0 X → Descent.Obl L X .mma →
      Descent.Steps L kernel Prod mem0 (Descent.Obl L) (Progress.rank L) X .mma :=
  fun _ hmax ho => Progress.mma_steps hmax (sync_guarded hpre hmax.1)
    (InputRing.operandSources hpre hmax.1 (threadFacts hpre hmax.1)
      (Region.inputAccessors hpre hmax.1 (threadFacts hpre hmax.1))) ho

/-- **A maximal execution has completed every tensor load.** -/
theorem tensor_obl (hpre : Pre P L mem0) :
    ∀ X, Maximal L kernel Prod mem0 X → Descent.Obl L X .tensor →
      Descent.Steps L kernel Prod mem0 (Descent.Obl L) (Progress.rank L) X .tensor :=
  fun _ hmax ho => Progress.tensor_steps hmax
    (InputRing.tensorSources hpre hmax.1 (threadFacts hpre hmax.1)) ho

end

end PTX.Kernels.Fp16Gemm8192.Proof
