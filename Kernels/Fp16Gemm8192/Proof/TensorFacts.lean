-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.Tensor
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The tensor branch of `Unsafe`

This file sits at the top of the proof tree, outside the layer order (as `MemoryFacts.lean` does):
it supplies the safety layer's tensor branch (`Safety.no_tensorUnsafe`) with the thread facts
(`threadFacts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

/-- **No tensor load is unsafe.** -/
theorem no_tensorUnsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : ¬ TensorUnsafe X :=
  Safety.no_tensorUnsafe hX (threadFacts hpre hX)

end

end PTX.Kernels.Fp16Gemm8192.Proof
