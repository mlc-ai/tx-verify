-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedRound
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedSumTail
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Numeric

noncomputable section

/-- The two statistics events precede the sole early probability publication of a repeat. -/
theorem repeatedEarlyCountOfStatistics {X : Execution} {g j endPos : Nat}
    {store notice : Event}
    (hStore : X.get (g,j) = some store) (hNotice : X.get (g,j+1) = some notice)
    (hStoreMark : earlyProbabilityMark store = false)
    (hNoticeMark : earlyProbabilityMark notice = false) (hAfter : j+2 ≤ endPos)
    (hRound : (((X.tr g).drop (j+2)).take (endPos-(j+2))).countP earlyProbabilityMark = 1) :
    ((X.tr g).take endPos).countP earlyProbabilityMark =
      ((X.tr g).take j).countP earlyProbabilityMark + 1 := by
  conv_lhs => rw [← Nat.add_sub_of_le hAfter,List.take_add,List.countP_append]
  rw [hRound,countP_take_succ_false hNotice hNoticeMark,
    countP_take_succ_false hStore hStoreMark]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (warp : Fin 8) (mixed : Bool) {g j b h row blocks visit : Nat} {t : TState} (old : ℝ)
    (oldRef newRef : Option ℝ) (chosen : Option ℝ) (word : Nat) (hWord : word < 2^32)
    (phase biasPhase scorePhase : Bool) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t r.affineStart [])
    (hRead : ∀ it ∈ shiftItems r.shiftRound, ∀ n ∈ it.reads, t.regs n = some (values n))
    (hSource : ∀ it ∈ shiftItems r.shiftRound, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems r.shiftRound,
      (scores it).1 = maskedLogit p b h row (visitKey blocks visit (it.x - r.rawBase)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks visit (it.y - r.rawBase)))
    (hScale : readERealPair l g t (.reg (shiftLayout r.shiftRound).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout r.shiftRound).addReg) =
      some (.ok (((-newRef.getD 0 : ℝ) : EReal), ((-newRef.getD 0 : ℝ) : EReal))))
    (hFrame : ∀ n ∈ r.numericFrame, t.regs n = some (values n))
    (hStage : r = .biased → values 637 = .pred ((stageOf warp).val = 1))
    (hMode : r = .biased → t.regs 634 = some (.pred mixed)) (hBase : values 2535 = b32 l.sharedBase)
    (hAddr : r = .unbiased → ∀ q,
      values (probabilityReg .unbiased q) = b32 (probabilityAddress l g (stageOf warp) q))
    (hSignal : r = .unbiased → values 5187 = b32 (l.sharedBase + 8 * (stageOf warp).val))
    (hWarp : values 1062 = b32 warp.val) (hOld : values 7257 = fl old)
    (hAlpha : valFloat .f32 (values r.alphaReg) = .ok (maskedRescale oldRef newRef))
    (hPhase : values 7258 = b32 phase.toNat) (continued : Nat → Value)
    (hContinued : ∀ n ∈ r.continuationRegs, t.regs n = some (continued n))
    (hChosen : continued 7256 = scoreValue chosen)
    (hCounter : continued (scoreLoopSite r.loop).word = b32 word)
    (hBiasPhase : r = .biased → continued 7250 = b32 biasPhase.toNat)
    (hScorePhase : continued 7253 = b32 scorePhase.toNat)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp r warp mixed old oldRef newRef chosen word hWord phase biasPhase scorePhase values scores
    ht hRead hSource hLogits hScale hOffset hFrame hStage hMode hBase hAddr hSignal hWarp hOld
    hAlpha hPhase continued hContinued hChosen hCounter hBiasPhase hScorePhase hRun

/-- The repeated affine scores, P publications and corrected sum lead to the next
head or its fallthrough, with the same selected maximum and denominator. -/
theorem repeatedNumericRoundPublishingPath :
    let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) (newRef.getD 0)
    let events := r.probabilityEvents l g (stageOf warp) weights
    let mass := old * maskedRescale oldRef newRef +
      (2 : ℝ) ^ (-newRef.getD 0) * maskedBlockSum (p.keyCount b row) blocks visit (weight p b h row)
    let site := scoreLoopSite r.loop
    let nextWord := (word+1)%2^32
    ∃ u endPos barInst, (∀ i : Fin events.length, X.get (g,j+i.val) = events[i.val]?) ∧
      X.get (g,j+events.length+1) =
        some ⟨probabilityWaitPc r.round true+1,.warpBar (2^32-1) barInst⟩ ∧
      j+events.length < endPos ∧
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg r.loop,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
        tailPhaseWords (!biasPhase) (!scorePhase) r.loop) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      (((X.tr g).drop j).take (endPos-j)).countP earlyProbabilityMark = 1 ∧
      (r = .biased → u.regs 7249 = some (continued 7249)) := by
  let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) (newRef.getD 0)
  let events := r.probabilityEvents l g (stageOf warp) weights
  obtain ⟨s,hEvents,hWait,hWeights,hFrameStore,hSaved,hTail,hStores⟩ :=
    repeatedProbabilitiesWithPath hp r (stageOf warp) mixed (newRef.getD 0) values scores ht
      hRead hSource
      hLogits hScale hOffset hFrame hStage hMode hBase hAddr hSignal hRun
  have hReg (n : Nat) (val : Value) (hn : n ∈ r.numericFrame) (hv : values n = val) :
      s.regs n = some val := (hFrameStore n hn).trans (congrArg some hv)
  have hAt : At s (probabilityWaitPc r.round true) (tailFrame l warp) := hWait.mono
    ⟨hReg 1062 _ (by cases r <;> decide) hWarp,
      hReg 2535 _ (by cases r <;> decide) hBase,trivial⟩
  have hPhaseRange : phase.toNat < 2 := by cases phase <;> decide
  obtain ⟨a,endPos,barInst,hEnd,hBar,hEntry,hWeightA,hOldA,hAlphaA,hPhaseA,hCont,hRest,hTailSum,
    hTailEarly⟩ :=
    repeatedTailSumEntryWithPath hp r warp phase.toNat hPhaseRange weights old hAt hWeights
      (hReg 7257 _ (by cases r <;> decide) hOld)
      (hReg r.alphaReg _ (by cases r <;> decide) rfl)
      (hReg 7258 _ (by cases r <;> decide) hPhase) continued
      (fun n hn => (hSaved n (Repeated.continuationRegs_mem hn)).trans (hContinued n hn)) hTail
  have hKeep (n : Nat) (hn : n ∈ r.continuationRegs) {v : Value} (hv : continued n = v) :
      a.regs n = some v := (hCont n hn).trans (congrArg some hv)
  obtain ⟨u,hu,hLocal,hBlock⟩ := repeatedSumAndLoopTailLocal (l := l) (g := g)
    r weights old (maskedRescale oldRef newRef)
    chosen word hWord phase biasPhase scorePhase hEntry hWeightA hOldA hAlphaA hAlpha
    (hKeep 7256 (by cases r <;> decide) hChosen)
    (hKeep _ (by cases r <;> decide) hCounter) hPhaseA
    (fun h => hKeep 7250 (by rw [h]; decide) (hBiasPhase h))
    (hKeep 7253 (by cases r <;> decide) hScorePhase)
  have hMass := shiftedBlockProducts p b h row blocks visit (newRef.getD 0) (fun _ => 1)
  simp only [mul_one] at hMass
  have hEnd' : j+events.length < endPos := hEnd
  refine ⟨u,endPos,barInst,hEvents,hBar,hEnd,(by simpa only [weights,hMass] using hu),
    hRest.after_local hLocal,?_,?_,?_⟩
  · have hPath := hStores.append (hTailSum.append (TraceReach.of_local hLocal))
    simp only [List.append_nil] at hPath
    rw [show endPos-j = events.length+(endPos-(j+events.length)) by omega,
      List.take_add,List.drop_drop]
    exact hPath
  · rw [show endPos-j = events.length+(endPos-(j+events.length)) by omega,
      List.take_add,List.drop_drop,List.countP_append,hTailEarly,Nat.add_zero]
    exact r.earlyCountOfEvents hEvents
  · intro hr
    exact (hBlock hr).trans (hCont 7249 (by rw [hr]; decide))

end
end PTX.Kernels.TmlFa4Fwd.Softmax
