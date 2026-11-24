-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemNumericCausality
public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Protocol.Statistics

/-- MMA BF16 inputs and finite FP32 coefficients at the actual softmax publications
suffice for stable sources throughout Tensor Memory, including rescale writeback. -/
theorem tensorSourcesOfOperandsAndRescaleStores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hOperands : CompletedMmaOperandsAreBf16 X)
    (hStores : RescaleStoreValuesAreF32 X) : SourceSafe l Assumptions.all X :=
  tensorSourcesOfOperandsAndRescaleStatistics hp hX hCuQ hOperands
    (rescaleStatisticsFiniteOfStores hp hX hCuQ hStores)

/-- The observed finite softmax coefficients also suffice for all completed MMA results. -/
theorem mmaCompletedValuesOfOperandsAndRescaleStores {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (hOperands : CompletedMmaOperandsAreBf16 X)
    (hStores : RescaleStoreValuesAreF32 X) : ∀ i, CompletedValues l Assumptions.all X i :=
  mmaCompletedValuesOfOperandsAndRescaleStatistics hp hX hCuQ hOperands
    (rescaleStatisticsFiniteOfStores hp hX hCuQ hStores)

end PTX.Kernels.TmlFa4Fwd.Safety
