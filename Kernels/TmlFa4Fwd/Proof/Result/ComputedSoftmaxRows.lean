-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.CompleteRecordedSoftmaxRows
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxNumericalLoop

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX

/-- Every completed live softmax row has its mathematical running denominator and
its actual probability and rescale publications in visit order. -/
theorem completedSoftmaxRowsOfComplete {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) :
    CompletedSoftmaxRows p l X := by
  apply completedSoftmaxRowsOfReplay hp
  intro producer hg stage hStage batch hb hLo hHi
  dsimp only
  intro hRow _
  exact Softmax.replayNumericalRowOfComplete hp hX hDone hFootprint hg stage hStage
    hb hLo hHi hRow

/-- The repeated output and LSE writers consume the same complete numerical history. -/
theorem repeatedValuesOfComplete {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) :
    RepeatedOutputValues p X ∧ Protocol.Statistics.RepeatedLseWriteValues p l X := by
  have hHistory := completedSoftmaxRowsOfComplete hp hX hDone hFootprint
  exact ⟨repeatedOutputValuesOfRecordedSoftmaxRows hp hX hDone hFootprint hHistory,
    repeatedLseWriteValuesOfRecordedSoftmaxRows hp hX hDone (hFootprint X hX) hHistory⟩

end PTX.Kernels.TmlFa4Fwd.Result
