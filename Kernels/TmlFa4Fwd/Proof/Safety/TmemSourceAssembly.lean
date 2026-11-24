-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccumulatorRescaleSources
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityProvenance

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX.TcMma

/-- The MMA source checks follow from the actual recorded operand and rescale values.
The separate ordinary-load source check applies to each register of a tensor load. -/
theorem tensorSourcesOfLoadAndNumericValues {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hOperands : CompletedMmaOperandsAreBf16 X)
    (hRescale : RescaleAccumulatorWordsAreF32 l X)
    (hLoad : ∀ i j cell, LoadCell l X i j cell →
      ∃ source value, ReadSource l X .ld source i cell ∧
        Wrote l Assumptions.all X source cell value) :
    SourceSafe l Assumptions.all X := by
  have hStored := storedAccumulatorIsF32OfRescale hp hX hCuQ hRescale
  have hMma := mmaCompletedValuesOfOperands hp hX hCuQ hOperands hStored
  exact sourceSafe_iff.mpr ⟨hLoad,
    fun _ _ hDone hRead => mmaAccumulatorValuesOfOperands hp hX hCuQ hOperands hStored hDone hRead,
    fun _ _ _ hRead => mmaProbabilityReadValue hp hX hCuQ hMma hRead⟩

end PTX.Kernels.TmlFa4Fwd.Safety
