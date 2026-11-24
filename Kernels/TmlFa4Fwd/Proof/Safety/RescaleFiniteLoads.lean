-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleStoreValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Thread.Correction Protocol.Statistics

/-- Finite actual MMA operands and softmax coefficients suffice for each actual
correction load to receive a finite FP32 accumulator word. -/
theorem rescaleLoadWordOfOperandsAndStores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hOperands : CompletedMmaOperandsAreBf16 X)
    (hStats : RescaleStoreValuesAreF32 X) :
    ∀ {load : EvId} {cell : Cell} {stage : Fin 2} {address j : Nat}
      {vals : List Value} {shape : TcShape},
      RescaleLoadCell l X load cell stage → X.TLd load address vals shape →
      LoadCell l X load j cell → ∃ x, vals[j]? = some (.float .f32 x) := by
  have hReads := rescaleStatisticsFiniteOfStores hp hX hCuQ hStats
  have hFactors := Thread.Correction.finiteRescaleFactorsOfReads hp hX hReads
  have hEntries : RescaleEntriesHaveFiniteAlpha l X := by
    intro writer cell stage value hFoot hWord
    obtain ⟨address,words,shape,j,hStore,hV,hCell⟩ := hWord
    have hCellStore : StoreCell l X writer cell :=
      ⟨address,words,shape,j,hStore,(List.getElem?_eq_some_iff.mp hV).1,hCell⟩
    exact Thread.Correction.rescaleChunkEntryOfFactor hp hX hFactors
      (outputRescaleStoreOfCell hp hX hCellStore hFoot)
  have hStep := rescaleFiniteStepOfEntries hp hX hCuQ hEntries
  obtain ⟨hMma,hStore⟩ := traceFiniteMmaAndRescale hp hX hCuQ hOperands hStep
  intro load cell stage address j vals shape hLoad he hCell
  exact rescaleLoadWordOfEarlierValues hp hX hCuQ hLoad he hCell
    (fun source _ hn hw => hMma source cell hn hw)
    (fun source _ v hFoot hw => hStore source cell stage v hFoot hw)

end PTX.Kernels.TmlFa4Fwd.Safety
