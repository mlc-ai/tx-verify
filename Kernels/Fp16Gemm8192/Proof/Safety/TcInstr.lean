-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcInstrResult

@[expose] public section

/-! # The MMA instruction branch of `Unsafe`, from the interface

An MMA of the kernel has a valid issue shape and a fully addressed operand footprint
(`issue_shape`) and its completed cells have values (`completed_values`); the kernel issues no
`tcgen05.cp` (`copy_safe`) and reuses no collector buffer (`collector_safe`). Its old values have
sources and it reads no Tensor Memory A operand (`mma_sources`, the MMA clauses of
`TcMma.SourceSafe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No MMA instruction is misused.** -/
theorem no_instructionUnsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) (hrel : MmaReleased L X) :
    ¬ InstructionUnsafe L Prod X :=
  fun h => h ⟨fun _ _ _ _ _ hi => ⟨issue_shape hpre hX ht hoc hi,
    completed_values hpre hX ht hoc hrel _⟩, copy_safe hX ht, collector_safe hX ht⟩

/-- **Every required Tensor Memory read of an MMA has a source**: the accumulator and A clauses of
`TcMma.SourceSafe`. -/
theorem mma_sources (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hoc : OperandCopies L X) (hrel : MmaReleased L X) :
    (∀ i cell, X.async.mmaDone i = true → X.MmaReadCell i cell →
      ∃ source value, ReadSource L X .acc source i cell ∧ Wrote L Prod X source cell value) ∧
    (∀ i cell, X.async.mmaDone i = true → X.MmaACell i cell →
      ∃ source value, ReadSource L X .a source i cell ∧ Wrote L Prod X source cell value) :=
  ⟨completed_accumulator_sources hpre hX ht hoc hrel, completed_a_sources hX ht⟩

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
