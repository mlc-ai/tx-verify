-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RecordedSoftmaxMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedRescaleInputs
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedWaitRun
import Kernels.TmlFa4Fwd.Proof.Thread.BiasedRescaleWindowFinish
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- The actual Bias poll inherits the prior maximum from previously recorded coefficient stores. -/
theorem ObservedBiasedRescaleInputs.priorMaximumOfEarlierPublications {p : Params}
    {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos : Nat} (entry : ObservedBiasedRescaleInputs p l X g pos)
    (hEarlier : EarlierRescaleMaximums l X g pos) :
    CanonicalMaximum entry.before 7251 := by
  obtain ⟨phase,o,hAt,hGet⟩ := entry.beforeEvent
  have hPrevious : EarlierRescaleMaximums l X g entry.biasWait := by
    intro k hk
    exact hEarlier k (by have := entry.waitBefore; have := entry.enterBefore; omega)
  obtain ⟨w,_,hPath,hMax,hEvent⟩ := maximumFrameOfEarlierPublications hp hX hFootprint
    hGet (by decide : 3420 ≤ 5181) (by decide : 5181 < 7742) hPrevious
  have hSame := reachedEventSourceUnique entry.beforePrefix hPath
    (stops_of_estep hAt) (stops_of_estep hEvent)
  exact hSame.symm ▸ priorMaximumAtBiasWait hMax (estep_source_pc hEvent).symm

/-- A biased visit publishes its updated maximum and its finite coefficient at the recorded
store. The entire path uses the same successful Bias poll and unpacked words. -/
theorem recordedBiasedRescaleMaximum {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos : Nat} {a : Acc} {bytes : List Byte} (he : StatisticsStore X (g,pos)
      (rescaleStore true) a bytes) (hEarlier : EarlierRescaleMaximums l X g pos) :
    ∃ v o, TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) v ∧
      EStep kernel Assumptions.all l g v ⟨(statsStore (rescaleStore true)).pc,.wr a bytes⟩ o ∧
      CanonicalMaximum v 7256 ∧
      ∃ old candidate, bytes = (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes := by
  obtain ⟨entry⟩ := observedBiasedRescaleInputs hp hX (hFootprint X hX) he
  obtain ⟨old,hOld⟩ := entry.priorMaximumOfEarlierPublications hp hX hFootprint hEarlier
  have hStart : entry.firstLoad ≤ entry.enter :=
    (Nat.le_add_right ..).trans (entry.firstBefore.trans entry.waitBefore.le)
  have hIndex := biasedAffineEntryIndex entry.checkpoint entry.continuation
    hStart entry.enterBefore entry.noneBefore he
  have hArithmetic := rescaleBiasedArithmeticEntryOfAffineInputsWithPath
    hp old entry.bias entry.dot entry.checkpoint entry.inverseScale entry.unpacked entry.packed
    (entry.prior.trans hOld) entry.scale (hIndex ▸ entry.continuation) he
  obtain ⟨u,_,prior,candidate,scale,hU,hScale,hInputs,hRun,_,_,_,hLocal⟩ := hArithmetic
  obtain ⟨v,o,hFinish,hStore,hNew,hBytes⟩ := rescaleSourceOfArithmeticEntry hp true
    prior candidate hScale hU hInputs hRun he
  have hMid : TraceReach kernel Assumptions.all l g entry.before
      (((X.tr g).drop entry.biasWait).take (entry.enter-entry.biasWait)) v := by
    have hQuiet := (TraceReach.of_local hLocal).append hFinish
    simpa only [List.append_nil] using entry.readyPath.append hQuiet
  have hSplit : (X.tr g).take entry.biasWait ++
      ((X.tr g).drop entry.biasWait).take (entry.enter-entry.biasWait) = (X.tr g).take pos := by
    have hTake : ((X.tr g).take entry.enter).take entry.biasWait =
        (X.tr g).take entry.biasWait := by
      rw [List.take_take,Nat.min_eq_left entry.waitBefore.le]
    rw [← List.drop_take,← hTake,List.take_append_drop,hIndex]
  exact ⟨v,o,hSplit ▸ entry.beforePrefix.append hMid,hStore,⟨_,hNew⟩,prior,candidate,hBytes⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
