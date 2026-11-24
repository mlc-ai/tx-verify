-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.PlainRescaleLoadOrigin
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPriorMaximum
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleAbiScale
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- The plain rescale store fixes the actual first score load of its visit.
The load has all four addresses and the live ABI scale registers. -/
theorem observedPlainRescalePathOfPriorMaximum {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g pos : Nat} {a : Acc} {data : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore false) a data) :
    ∃ start t ending,
      start+8 = pos ∧ At t (scorePc .unbiased 0) [] ∧
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take start) t ∧
      (∃ out address values, X.get (g,start) =
        some ⟨scorePc .unbiased 0,.tc (.ld address values .s32x32b)⟩ ∧
        EStep kernel Assumptions.all l g t ⟨scorePc .unbiased 0,.tc (.ld address values .s32x32b)⟩
          out) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop start) ending ∧
      (CanonicalMaximum t 7255 → ∃ scores : Nat → Option ℝ,
        RescaleArithmeticEntryWith p l X (g,pos) false (fun u =>
          TraceReach kernel Assumptions.all l g t (((X.tr g).drop start).take 8) u ∧
          RescaleShiftScales p false u ∧
          ∀ (q : Fin 4) (k : Fin 16), u.regs (repeatedScorePairReg .unbiased q k.val) =
            some (.pair (scoreValue (scores (32*q.val+2*k.val)))
              (scoreValue (scores (32*q.val+(2*k.val+1))))))) := by
  obtain ⟨start,address,words,hIdx,hLoad⟩ := plainRescaleScoreOrigin hp hX he
  obtain ⟨w,hw,_,_,_,_,_,_⟩ :=
    softmaxBodySuffix hp hX hLoad (by decide : 3420 ≤ 6679) (by decide : 6679 < 7742)
  obtain ⟨warp,_,entry,s,ending,hBefore,hs,hPast,hRun⟩ :=
    softmaxRoleEntryRecorded hp hX hLoad (by decide : 173 < 6679) (by decide : 6679 ≠ 3102)
      (hw ▸ w.isLt)
  obtain ⟨t,o,ht,hAddr,hEvent,hTail,hReach⟩ :=
    unbiasedScoreStartFromEntry hp warp hs hRun hLoad hBefore
  obtain ⟨u,_,huPc,_,_,_,_,hScale,hOther,_,hOtherPath⟩ :=
    softmaxRoleEventFromEntryWithScratch hp warp hs hRun hLoad hBefore
      (by decide : 6679 < 7742) (initialShiftScaleFrame p hs.1)
      (fun hLo hHi hSub _ _ _ hFrame hStep =>
        shiftScaleFrameStep hp hLo hHi hSub hFrame hStep)
  have hSame := reachedEventSourceUnique hReach hOtherPath
    (stops_of_estep hEvent) (stops_of_estep hOther)
  subst u
  have hScalar := shiftScaleAbiAtScoreLoad false hScale huPc
  obtain ⟨hNeg,hPair⟩ := shiftScalesOfFrame hScale
    (huPc.symm ▸ (by decide : 4399 ≤ 6679)) (huPc.symm ▸ (by decide : 6679 ≤ 7604))
  have hPath : TraceReach kernel Assumptions.all l g {} ((X.tr g).take start) t := by
    have hSplit : (X.tr g).take entry ++ ((X.tr g).drop entry).take (start-entry) =
        (X.tr g).take start := by
      have hTake : ((X.tr g).take start).take entry = (X.tr g).take entry := by
        rw [List.take_take,Nat.min_eq_left hBefore]
      rw [← List.drop_take,← hTake,List.take_append_drop]
    rw [← hSplit]
    exact hPast.append hReach
  refine ⟨start,t,ending,hIdx,ht,hPath,⟨o,address,words,hLoad,hEvent⟩,hTail,fun hPrior => ?_⟩
  obtain ⟨old,hOld⟩ := hPrior
  have hStore : StatisticsStore X (g,start+8) (rescaleStore false) a data := hIdx.symm ▸ he
  obtain ⟨scores,hArithmetic⟩ := rescalePlainArithmeticEntryOfLoadsWithPath hp hX hFrame
    (stageOf warp) old ht hAddr hOld hScalar hTail hStore
  refine ⟨scores,hIdx ▸ hArithmetic.mono (fun v hv => ⟨hv.1,⟨?_,fun _ => ?_⟩,hv.2.1⟩)⟩
  · exact (hv.2.2 1230 (by decide) (by decide +kernel)).trans hNeg
  · exact (hv.2.2 8692 (by decide) (by decide +kernel)).trans
      (hPair (huPc.symm ▸ (by decide : 6660 ≤ 6679)))

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
