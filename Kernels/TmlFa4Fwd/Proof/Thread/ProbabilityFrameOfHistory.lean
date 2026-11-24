-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedPlainProbabilityFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedProbabilityFrame
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleMaximumHistory
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedWaitRun
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

/-- On either repeated path, the actual earlier rescale publications determine
the carried maximum at the chosen probability publication. -/
theorem repeatedProbabilityFrameOfExecution {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (mode : Repeated) {g pos : Nat} {a : Acc} {data : List Byte}
    (hWrite : StatisticsStore X (g,pos) (rescaleStore (decide (mode = .biased))) a data)
    (hPresent : pos+2 < (X.tr g).length) :
    RepeatedProbabilityAfterCoefficient p l X mode g pos := by
  cases mode
  · apply biasedProbabilityFrameOfObservedCoefficient hp hX (hFootprint X hX) hWrite hPresent
    intro entry
    obtain ⟨phase,o,hEvent,hGet⟩ := entry.beforeEvent
    obtain ⟨s,v,hPath,hMax,hStep⟩ := recordedMaximumFrame hp hX hFootprint hGet
      (by change 3420 ≤ 5181; decide) (by change 5181 < 7742; decide)
    have hSame := reachedEventSourceUnique entry.beforePrefix hPath
      (stops_of_estep hEvent) (stops_of_estep hStep)
    exact hSame.symm ▸ priorMaximumAtBiasWait hMax (estep_source_pc hStep).symm
  · apply plainProbabilityFrameOfObservedCoefficient hp hX (hFootprint X hX) hWrite hPresent
    intro warp roleEntry start seed t ending o address words _ _ hPrefix _ hBefore _ hGet
      hEvent hPath
    have hSplit : (X.tr g).take start = (X.tr g).take roleEntry ++
        ((X.tr g).drop roleEntry).take (start-roleEntry) := by
      conv_lhs => rw [← List.take_append_drop roleEntry ((X.tr g).take start)]
      rw [List.take_take,Nat.min_eq_left hBefore,List.drop_take]
    have ht : TraceReach kernel Assumptions.all l g {} ((X.tr g).take start) t := by
      rw [hSplit]
      exact hPrefix.append hPath
    obtain ⟨s,v,hWhole,hMax,hStep⟩ := recordedMaximumFrame hp hX hFootprint hGet
      (by change 3420 ≤ 6679; decide) (by change 6679 < 7742; decide)
    have hSame := reachedEventSourceUnique ht hWhole
      (stops_of_estep hEvent) (stops_of_estep hStep)
    exact hSame.symm ▸ priorMaximumAtPlainLoad hMax (estep_source_pc hStep).symm

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
