-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstr
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Sources
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts
public import Kernels.Fp16Gemm8192.Proof.TmemAccessFacts

@[expose] public section

/-! # The MMA instruction branch of `Unsafe`

This file sits at the top of the proof tree, outside the layer order (as `TensorFacts.lean` does):
it supplies the safety layer's MMA instruction branch (`Safety.no_instructionUnsafe`) with the input
ring's operand copies (`InputRing.operandCopies`, over the region layer's input accessors) and the
accumulators' lifetimes (`mmaReleased`, from the Tensor Memory access branch), all from the thread
facts (`threadFacts`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

/-- **No MMA instruction is misused.** -/
theorem no_instructionUnsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ TcMma.InstructionUnsafe L Prod X :=
  have ht := threadFacts hpre hX
  Safety.no_instructionUnsafe hpre hX ht
    (InputRing.operandCopies hpre hX ht (Region.inputAccessors hpre hX ht)) (mmaReleased hpre hX)

end

end PTX.Kernels.Fp16Gemm8192.Proof
