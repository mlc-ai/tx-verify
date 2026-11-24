-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RecordedBiasedMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.RecordedPlainMaximum
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- Each actual rescale store has a canonical updated maximum and finite coefficient. -/
theorem recordedRescaleMaximumAndData {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos : Nat} (biased : Bool) {a : Acc} {bytes : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore biased) a bytes) :
    ∃ v o, TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) v ∧
      EStep kernel Assumptions.all l g v ⟨(statsStore (rescaleStore biased)).pc,.wr a bytes⟩ o ∧
      CanonicalMaximum v 7256 ∧
      ∃ old candidate, bytes = (alphaWord (abiFloat p.scaleLog2Bits) old candidate).toBytes := by
  revert biased a bytes
  induction pos using Nat.strong_induction_on with
  | h pos ih =>
    intro biased a bytes he
    have hEarlier : EarlierRescaleMaximums l X g pos := by
      intro j hj biased a bytes t o he hPath hEvent
      obtain ⟨u,_,hEarlier,hPublish,hMax,_⟩ := ih j hj biased he
      have hSame := reachedEventSourceUnique hPath hEarlier
        (stops_of_estep hEvent) (stops_of_estep hPublish)
      exact hSame.symm ▸ hMax
    cases biased
    · exact recordedPlainRescaleMaximum hp hX hFootprint he hEarlier
    · exact recordedBiasedRescaleMaximum hp hX hFootprint he hEarlier

/-- Every recorded role occurrence inherits the running maximum from its own history. -/
theorem recordedMaximumFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g pos : Nat} {target : Event} (he : X.get (g,pos) = some target)
    (hLo : 3420 ≤ target.pc) (hHi : target.pc < 7742) :
    ∃ v o, TraceReach kernel Assumptions.all l g {} ((X.tr g).take pos) v ∧
      MaximumFrame v ∧ EStep kernel Assumptions.all l g v target o := by
  apply maximumFrameOfEarlierPublications hp hX hFootprint he hLo hHi
  intro j _ biased a bytes t o he hPath hEvent
  obtain ⟨v,_,hEarlier,hStore,hMax,_⟩ := recordedRescaleMaximumAndData hp hX hFootprint biased he
  have hSame := reachedEventSourceUnique hPath hEarlier
    (stops_of_estep hEvent) (stops_of_estep hStore)
  exact hSame.symm ▸ hMax

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
