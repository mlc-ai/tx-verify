-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityNumeric
public import Kernels.TmlFa4Fwd.Proof.Thread.PlainRescaleLoadOrigin
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxRecordedEntry
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleAbiScale
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxProbabilityRegisters
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPriorMaximum
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait
import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def plainProbabilityCarry : List Nat :=
  [1062,2535,5127,5176,5177,5187,7257,7258,1230,8692,5183,5185,5181,5184]

private def plainProbabilityKeeps (r : Nat) : Bool :=
  !(rescaleMaxWrites false).contains r && !(oWrites (alphaSite false).items).contains r &&
    (List.finRange 4).all (fun q =>
      decide (r < repeatedScoreWordBase .unbiased q ∨
        repeatedScoreWordBase .unbiased q+32 ≤ r) &&
      (List.finRange 16).all (fun k => r != repeatedScorePairReg .unbiased q k.val))

private theorem plainProbabilityKeepAudit :
    plainProbabilityCarry.all plainProbabilityKeeps = true := by decide +kernel

private theorem plainPairKeepAudit :
    (List.finRange 4).all (fun q => (List.finRange 16).all
      (fun k => !((oWrites (alphaSite false).items).contains
        (repeatedScorePairReg .unbiased q k.val)))) = true := by decide +kernel

private theorem canonicalPairedScale {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (hScale : t.regs 8692 = some (joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits))) :
    readERealPair l g t (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))) := by
  let word := b32 p.scaleLog2Bits
  have hb : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits)
    (by simp [Params.scalarWords])).1
  obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
  have hVal : valFloat .f32 word = .ok (abiFloat p.scaleLog2Bits) := by
    simpa only [word,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  have hSplit : splitValue 64 (joinValue word word) = (word,word) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hb)
  exact readERealPair_reg hScale (by rw [hSplit]; exact hVal) (by rw [hSplit]; exact hVal)

/-- Once the real plain load's carried maximum is canonical, its coefficient
and probability words follow from the same actual prefix. -/
theorem plainProbabilityFrameOfObservedLoad {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (warp : Fin 8) {g start entry pos : Nat}
    (hWarp : warp.val = Prologue.warpIndex l g) {s t : TState} {o ending : Option TState}
    (hs : At s 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)])
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop entry) ending)
    (hBefore : entry ≤ start) {address : Nat} {words : List Value}
    (he : X.get (g,start) = some ⟨scorePc .unbiased 0,.tc (.ld address words .s32x32b)⟩)
    (hSource : EStep kernel Assumptions.all l g t
      ⟨scorePc .unbiased 0,.tc (.ld address words .s32x32b)⟩ o)
    (hPath : TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (start-entry)) t)
    (hOld : CanonicalMaximum t 7255)
    (hIndex : start+8 = pos) {a : Acc} {data : List Byte}
    (hWrite : StatisticsStore X (g,pos) (rescaleStore false) a data)
    (hPresent : pos+2 < (X.tr g).length) :
    RepeatedProbabilityAfterCoefficient p l X .unbiased g pos := by
  subst pos
  obtain ⟨u,_,hu,hAddrs,hU,hUTail,hUPath,hGeom⟩ :=
    unbiasedScoreStartWithProbabilityGeometryFromEntry hp warp hs hr he hBefore
  have hEqU := reachedEventSourceUnique hPath hUPath (stops_of_estep hSource) (stops_of_estep hU)
  subst u
  obtain ⟨v,_,hvPc,_,hWarpHeld,hShared,_,hScale,hV,_,hVPath⟩ :=
    softmaxRoleEventFromEntryWithScratch hp warp hs hr he hBefore
      (by decide : 6679 < 7742) (initialShiftScaleFrame p hs.1)
      (fun hLo hHi hSub _ _ _ hf hStep => shiftScaleFrameStep hp hLo hHi hSub hf hStep)
  have hEqV := reachedEventSourceUnique hPath hVPath (stops_of_estep hSource) (stops_of_estep hV)
  subst v
  obtain ⟨w,_,hW,hWPath,hMass,hPhase⟩ :=
    probabilityCarryRegistersFromEntry hp warp hs hr he hBefore
      (by change 5005 < 6679; decide) (by change 6679 ≤ 7604; decide)
  have hEqW := reachedEventSourceUnique hPath hWPath (stops_of_estep hSource) (stops_of_estep hW)
  subst w
  have hAbi := shiftScaleAbiAtScoreLoad false hScale hvPc
  obtain ⟨hNegative,hPaired⟩ := shiftScalesOfFrame hScale
    (hvPc.symm ▸ (by decide : 4399 ≤ 6679)) (hvPc.symm ▸ (by decide : 6679 ≤ 7604))
  obtain ⟨old,hPrior⟩ := hOld
  obtain ⟨scores,hArithmetic⟩ := rescalePlainArithmeticEntryOfLoadsWithPairs
    hp hX hFrame (stageOf warp) old hu hAddrs hPrior hAbi hUTail hWrite
  obtain ⟨tA,endingA,oldA,candidate,scaleWord,hAt,hScaleWord,hInputs,hTail,hPairs,hCarry⟩ :=
    hArithmetic
  have hMore := recordedProbabilitySuffixNonempty (g := g) (j := start+8) hTail
    (Or.inr (by omega))
  obtain ⟨tP,hPC,hPTail,hPreserve⟩ := alphaTraceWithScaleWordInPrefix false
    (scalePositive hp).1 oldA candidate hScaleWord hAt hInputs hTail hMore
  have keep (r : Nat) (hr : r ∈ plainProbabilityCarry) : tP.regs r = t.regs r := by
    have h := List.all_eq_true.mp plainProbabilityKeepAudit r hr
    simp only [plainProbabilityKeeps,Bool.and_eq_true,Bool.not_eq_true',List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    have hScores (q : Fin 4) := List.all_eq_true.mp h.2 q (List.mem_finRange q)
    exact (hPreserve r h.1.2).trans (hCarry r
      (fun q => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp (hScores q)).1,fun k =>
        bne_iff_ne.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hScores q)).2 k
          (List.mem_finRange k))⟩) h.1.1)
  have hScores (q : Fin 4) (k : Fin 16) :=
    (hPreserve _ (by
      have hQuarter := List.all_eq_true.mp plainPairKeepAudit q (List.mem_finRange q)
      simpa using List.all_eq_true.mp hQuarter k (List.mem_finRange k))).trans (hPairs q k)
  let stage := stageOf warp
  have hGeomRows : Holds t.regs (unbiasedAddressRows l g warp).tail := by
    exact ((holds_append ..).mp hGeom.2.2).1
  have hPSlot (q : Fin 4) : t.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g stage q)) := by
    apply holds_mem ((holds_append ..).mp hGeom.2.2).2
    fin_cases q <;> simp [stage,unbiasedProbabilityFacts,probabilityReg]
  have hAddrP (q : Fin 4) : tP.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g stage q)) :=
    (keep _ (by fin_cases q <;> decide)).trans (hPSlot q)
  have hVals : ∀ r ∈ unbiasedExpFrame, ∃ v, tP.regs r = some v := by
    intro r hr
    simp only [unbiasedExpFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,(keep _ (by decide)).trans hWarpHeld⟩
    · exact ⟨_,(keep _ (by decide)).trans hShared⟩
    · exact ⟨_,hPC.2.2.2.2.2.2.1⟩
    · obtain ⟨v,hv⟩ := hMass
      exact ⟨v,(keep _ (by decide)).trans hv⟩
    · obtain ⟨v,hv⟩ := hPhase
      exact ⟨v,(keep _ (by decide)).trans hv⟩
    · exact ⟨_,hAddrP 0⟩
    · exact ⟨_,hAddrP 1⟩
    · exact ⟨_,hAddrP 2⟩
    · exact ⟨_,hAddrP 3⟩
    · exact ⟨_,(keep _ (by decide)).trans hGeom.2.1⟩
  have hFrameP : At tP 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
      (1492,alphaWord (abiFloat p.scaleLog2Bits) oldA candidate)] :=
    hPC.mono ⟨(keep _ (by decide)).trans hGeomRows.2.1,
      (keep _ (by decide)).trans hGeomRows.1,(keep _ (by decide)).trans hShared,
      (keep _ (by decide)).trans hGeom.1,hPC.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨sP,hNumber,hSuffix⟩ :=
    plainProbabilityFrameAfterAlpha hp warp hWarp oldA candidate scores
      hFrameP hPC.2.2.2.2.2.1 ((keep _ (by decide)).trans hNegative)
      (canonicalPairedScale hp ((keep _ (by decide)).trans
        (hPaired (hvPc.symm ▸ (by decide : 6660 ≤ 6679)))))
      hScores hVals hAddrP ((keep _ (by decide)).trans hGeom.2.1) hPTail (.inr hPresent)
  exact ⟨stage,sP,endingA,scores,_,hNumber,hSuffix⟩


/-- The exact predecessor of the recorded coefficient uniquely supplies this
round's scores. Only the history of its carried reference remains an input. -/
theorem plainProbabilityFrameOfObservedCoefficient {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g pos : Nat} {a : Acc} {data : List Byte}
    (hWrite : StatisticsStore X (g,pos) (rescaleStore false) a data)
    (hPresent : pos+2 < (X.tr g).length)
    (hHistory : ∀ (warp : Fin 8) (entry start : Nat) (s t : TState)
      (ending o : Option TState) (address : Nat) (words : List Value),
      warp.val = Prologue.warpIndex l g →
      At s 3103 [(1062,b32 warp.val),(2535,b32 l.sharedBase)] →
      TraceReach kernel Assumptions.all l g {} ((X.tr g).take entry) s →
      Run kernel Assumptions.all l g s ((X.tr g).drop entry) ending →
      entry ≤ start → start+8 = pos →
      X.get (g,start) = some ⟨scorePc .unbiased 0,.tc (.ld address words .s32x32b)⟩ →
      EStep kernel Assumptions.all l g t
        ⟨scorePc .unbiased 0,.tc (.ld address words .s32x32b)⟩ o →
      TraceReach kernel Assumptions.all l g s (((X.tr g).drop entry).take (start-entry)) t →
      CanonicalMaximum t 7255) :
    RepeatedProbabilityAfterCoefficient p l X .unbiased g pos := by
  obtain ⟨start,address,words,hIndex,hLoad⟩ := plainRescaleScoreOrigin hp hX hWrite
  obtain ⟨w',hw',_⟩ :=
    softmaxBodySuffix hp hX hLoad (by decide : 3420 ≤ 6679) (by decide : 6679 < 7742)
  obtain ⟨warp,hWarp,entry,s,ending,hBefore,hs,hOrigin,hRun⟩ :=
    softmaxRoleEntryRecorded hp hX hLoad (by decide : 173 < 6679) (by decide : 6679 ≠ 3102)
      (hw' ▸ w'.isLt)
  obtain ⟨t,o,_,_,hSource,_,hPath⟩ :=
    unbiasedScoreStartFromEntry hp warp hs hRun hLoad hBefore
  have hOld := hHistory warp entry start s t ending o address words hWarp hs hOrigin hRun
    hBefore hIndex hLoad hSource hPath
  exact plainProbabilityFrameOfObservedLoad hp hX hFrame warp hWarp hs hRun hBefore
    hLoad hSource hPath hOld hIndex hWrite hPresent

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
