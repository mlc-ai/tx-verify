-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityOperandFinite
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityFrameOfHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Kernels.TmlFa4Fwd.Thread.Scores

/-- The observed earlier maxima close the probability words of each selected
later publication consumed by a completed PV operand. -/
theorem laterCompletedPvProbabilitiesOfExecution {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) :
    LaterCompletedPvProbabilitiesAreBf16 l X := by
  have hCuQ := ((hFootprint X hX).metadataProtected hp).1
  apply laterCompletedPvProbabilitiesOfFrames hp hX _ hCuQ
  intro mode g pos a data hWrite hPresent
  exact repeatedProbabilityFrameOfExecution hp hX hFootprint mode hWrite hPresent

/-- All completed PV instructions receive finite BF16 probability elements from
their actual opening or repeated publication. -/
theorem completedPvProbabilitiesOfExecution {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) :
    Safety.CompletedPvProbabilitiesAreBf16 X :=
  probabilitiesBf16OfLaterCompletedReads hp hX hFootprint
    (laterCompletedPvProbabilitiesOfExecution hp hX hFootprint)

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
