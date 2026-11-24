-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemLoadSourceCases
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemFinalLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemScoreLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemSourceAssembly

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread

/-- An actual ordinary Tensor Memory load is supported by its stable writer. -/
theorem ordinaryLoadSourceValue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {load : EvId} {j : Nat} {cell : Cell} (hLoad : LoadCell l X load j cell) :
    ∃ source value, ReadSource l X .ld source load cell ∧
      Wrote l Assumptions.all X source cell value := by
  rcases loadCellCases hp hX hLoad with ⟨_,hScore⟩ | ⟨_,hRescale⟩ | ⟨_,hFinal⟩
  · exact scoreLoadSourceValue hp hX hCuQ hValues hScore
  · exact rescaleLoadSourceValue hp hX hCuQ hValues hRescale
  · exact finalizationLoadSourceValue hp hX hCuQ hValues hFinal

/-- Every required Tensor Memory read has a stable source when the actual numerical
operands and correction words have their kernel formats. -/
theorem tensorSourcesOfNumericValues {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hOperands : CompletedMmaOperandsAreBf16 X)
    (hRescale : RescaleAccumulatorWordsAreF32 l X) :
    SourceSafe l Assumptions.all X := by
  have hStored := storedAccumulatorIsF32OfRescale hp hX hCuQ hRescale
  have hMma := mmaCompletedValuesOfOperands hp hX hCuQ hOperands hStored
  exact tensorSourcesOfLoadAndNumericValues hp hX hCuQ hOperands hRescale
    (fun _ _ _ hLoad => ordinaryLoadSourceValue hp hX hCuQ hMma hLoad)

end PTX.Kernels.TmlFa4Fwd.Safety
