-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RescaleStatisticsSources
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleMaximumHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX

/-- The output footprint yields finite rescale values on every consistent trace prefix. -/
theorem rescaleStoreValuesOfOutputFootprint {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) :
    RescaleStoreValuesAreF32 X := by
  intro i biased a data hStore
  obtain ⟨_,_,_,_,_,old,candidate,hData⟩ :=
    Thread.Scores.recordedRescaleMaximumAndData hp hX hFootprint biased hStore
  exact ⟨_,_,hData,rescaleFactorOfSoftmaxWord _ old candidate⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
