-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RecordedSoftmaxMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedPlainRescale
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- A plain visit inherits its prior maximum from publications before the actual first score load.
The returned path ends at the source of the recorded coefficient store. -/
theorem recordedPlainRescaleMaximum {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos : Nat} {a : Acc} {bytes : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore false) a bytes)
    (hEarlier : EarlierRescaleMaximums l X g pos) :
    ∃ v o, TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) v ∧
      EStep kernel Assumptions.all l g v ⟨(statsStore (rescaleStore false)).pc,.wr a bytes⟩ o ∧
      CanonicalMaximum v 7256 ∧
      ∃ old candidate, bytes = (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes := by
  obtain ⟨j,t,_,hIndex,ht,hStart,⟨o,addr,words,hGet,hAt⟩,_,hArithmetic⟩ :=
    observedPlainRescalePathOfPriorMaximum hp hX (hFootprint X hX) he
  have hPrevious : EarlierRescaleMaximums l X g j := by
    intro k hk
    exact hEarlier k (by omega)
  obtain ⟨w,_,hPath,hMax,hEvent⟩ := maximumFrameOfEarlierPublications hp hX hFootprint
    hGet (by decide : 3420 ≤ 6679) (by decide : 6679 < 7742) hPrevious
  obtain rfl := reachedEventSourceUnique hStart hPath (stops_of_estep hAt) (stops_of_estep hEvent)
  have hPrior := priorMaximumAtPlainLoad hMax ht.1
  obtain ⟨_,entry⟩ := hArithmetic hPrior
  obtain ⟨u,_,prior,candidate,scale,hU,hScale,hInputs,hRun,hFromLoad,_,_⟩ := entry
  obtain ⟨v,o,hLocal,hStore,hNew,hBytes⟩ := rescaleSourceOfArithmeticEntry hp false
    prior candidate hScale hU hInputs hRun he
  have hMid : TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 8) v := by
    simpa only [List.append_nil] using hFromLoad.append hLocal
  have hSplit : (X.tr g).take j ++ ((X.tr g).drop j).take 8 = (X.tr g).take pos := by
    have hTake : ((X.tr g).take pos).take j = (X.tr g).take j := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    have hDrop := List.drop_take (l := X.tr g) (i := j) (j := pos)
    rw [show pos-j = 8 by omega] at hDrop
    rw [← hDrop,← hTake,List.take_append_drop]
  exact ⟨v,o,hSplit ▸ hStart.append hMid,hStore,⟨_,hNew⟩,prior,candidate,hBytes⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
