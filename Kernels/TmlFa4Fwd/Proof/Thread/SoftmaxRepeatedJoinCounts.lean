-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasedVisitBody
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailAlignment
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- `warpRepeatedProbabilityJoinFromShiftWithControlOfMaximal` that also reports the four
counts at the join: the six Tensor Memory collectives of the packet, one warp barrier, one
election and no statistics notice. -/
theorem warpRepeatedProbabilityJoinWithCountsOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {lead : Nat} (mode : Repeated) (stage : Fin 2) (ordinal bars elects : Nat)
    (scores : Nat → Nat → Option ℝ) (reference : Nat → ℝ)
    (warp : Nat → Fin 8) (old alpha : Nat → ℝ) (phase : Nat → Nat)
    {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g mode.affineStart (F g))
    (hFrame : ∀ g (hw : SameWarp l lead g),
      RepeatedProbabilityShiftFrame p l mode g stage (input g hw).ready (scores g) (reference g))
    (hOperands : ∀ g (hw : SameWarp l lead g),
      RepeatedTailOperands l mode stage (input g hw).ready (warp g) (old g) (alpha g) (phase g))
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP isTcColl = ordinal)
    (hBar : ∀ g (hw : SameWarp l lead g), warpBars X g (input g hw).pos = bars)
    (hElect : ∀ g (hw : SameWarp l lead g), elections X g (input g hw).pos = elects)
    (notices credits scorePolls : Nat → Nat)
    (hNotices : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP Thread.Scores.publishesStats = notices g)
    (hCredits : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP Thread.Scores.creditAcquired = credits g)
    (hScores : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP scoreAcquired = scorePolls g) :
    ∀ g (hw : SameWarp l lead g),
      let start := (input g hw).pos
      let delay := if mode = .biased then 1 else 0
      let weights := fun i =>
        repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
      ∃ leader : Fin 32,
        ∃ j : RepeatedProbabilityJoinCursor l X g mode (warp g) weights (old g) (alpha g)
            (phase g),
          (∀ q : Fin 4, X.get (g,start+mode.probabilityStoreOffset q) =
            some (repeatedStoreEvent l g stage mode.round q weights)) ∧
          Thread.Scores.ProbabilityCredit l X (g,start+delay+4) (g/l.block) stage 0 ∧
          (laneOf l g = leader.val →
            Thread.Scores.ProbabilityCredit l X (g,start+delay+9) (g/l.block) stage 1) ∧
          j.cursor.ending = (input g hw).ending ∧
          (∀ n ∈ mode.continuationRegs,
            (input g hw).ready.regs n = some (j.values n)) ∧
          SoftmaxCounts X g j.cursor.pos (ordinal+delay+6) (bars+1) (elects+1) (notices g)
            (credits g) (scorePolls g) ∧
          (∃ inst, X.Elect (g,start+delay+8) (probabilityWaitPc mode.round true+2) (2^32-1)
            inst leader.val) ∧
          start+delay+9 ≤ j.cursor.pos ∧
          (laneOf l g = leader.val → start+delay+9 < j.cursor.pos) := by
  classical
  let delay := if mode = .biased then 1 else 0
  let weights g i :=
    repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-(reference g)) (scores g i))
  have trace := warpRepeatedProbabilityTraceWithFrameOfMaximal hp hMax mode stage ordinal scores
    reference input hFrame hRank
  choose tail hStores hCredit hTailWait hPos hEnding hWeights hTc hDelayed hWait hKeep using trace
  let values g n := if h : SameWarp l lead g
    then ((tail g h).ready.regs n).getD (.pred false) else .pred false
  have hValue (g : Nat) (hw : SameWarp l lead g) (n : Nat) {v : Value}
      (he : (tail g hw).ready.regs n = some v) : values g n = v := by
    simp only [values,dite_eq_left hw,he,Option.getD_some]
  let carried g := tailCarryWith l (warp g) mode.round (some (values g)) true
  let ready (g : Nat) (hw : SameWarp l lead g) :
      OpeningTripCursor l X g (probabilityWaitPc mode.round true+1) (carried g) :=
    let c := tail g hw
    have hDef := repeatedTailFrameDefined (hOperands g hw) (hKeep g hw) (hWeights g hw)
    have hReg n (hn : n ∈ tailLiveWith mode.round true) :
        c.ready.regs n = some (values g n) := by
      obtain ⟨v,hv⟩ := hDef.1 n hn
      rw [hValue g hw n hv]
      exact hv
    ⟨c.pos,c.before,c.ready,c.ending,c.positive,c.bounded,c.released,
      c.checkpoint.mono (repeatedFrameHolds (values g) hDef.2 hReg),c.recorded,c.remaining,
      c.localSteps⟩
  have hTailRanks (g : Nat) (hw : SameWarp l lead g) :
      warpBars X g (ready g hw).pos = bars ∧ elections X g (ready g hw).pos = elects := by
    have hCounts := repeatedProbabilityTailOrdinals mode stage (weights g) (hStores g hw)
      (hDelayed g hw) (hWait g hw) (hCredit g hw) (hTailWait g hw)
    change (warpBars X g (tail g hw).pos = bars ∧ elections X g (tail g hw).pos = elects)
    rw [hPos g hw]
    exact ⟨hCounts.1.trans (hBar g hw),hCounts.2.trans (hElect g hw)⟩
  have next := warpTailProbabilityBarrierOfMaximal hp hMax mode.round bars ready
    (fun g hw => (hTailRanks g hw).1)
  choose bar post hBarGet hBarPos hBarRegs hBarEnding hNextRank using next
  have hElectionRank (g : Nat) (hw : SameWarp l lead g) :
      elections X g (post g hw).pos = elects := by
    obtain ⟨pc,hGet⟩ := hBarGet g hw
    rw [hBarPos g hw]
    exact (countP_take_succ_false (p := isElectEv) hGet rfl).trans (hTailRanks g hw).2
  have hFresh (g : Nat) (pair : Nat × Value) (h : pair ∈ carried g) :
      pair.1 ≠ tailElectLane mode.round ∧ pair.1 ≠ tailElectPred mode.round := by
    rcases tailCarryWith_member h with hm | hm | hm
    · rw [hm]
      cases mode <;> decide
    · rw [hm]
      cases mode <;> decide
    · exact ⟨(tailLiveDistinct _ _ hm).1,(tailLiveDistinct _ _ hm).2.1⟩
  intro g hw
  obtain ⟨inst,leader,u,he,hUPos,hUEnd,hURank⟩ :=
    warpTailProbabilityElectionOfMaximal hp hMax mode.round elects post hElectionRank
      (fun g pair hm => (hFresh g pair hm).1) (fun g pair hm => (hFresh g pair hm).2) g hw
  let chosen := laneOf l g == leader.val
  let payload : OpeningTripCursor l X g (probabilityWaitPc mode.round true+3)
      ((tailElectPred mode.round,.pred chosen)::carried g) :=
    ⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,
      u.checkpoint.mono ⟨u.checkpoint.2.2.2.2.1,u.checkpoint.2.2.2.2.2.2⟩,
      u.recorded,u.remaining,u.localSteps⟩
  obtain ⟨joined,hTailCredit,hJoinPos,hJoinEnding⟩ :=
    repeatedProbabilityTailJoinOfMaximal hp hMax hw.1.2.1 mode.round (warp g)
      (some (values g)) true chosen payload
  have hJoinPc : (signalSite (tailPublication mode.round)).pc+1 =
      (signalSite mode.tailSignal).pc+1 := by cases mode <;> rfl
  let hJoined : OpeningTripCursor l X g ((signalSite mode.tailSignal).pc+1) (carried g) :=
    ⟨joined.pos,joined.before,joined.ready,joined.ending,joined.positive,joined.bounded,
      joined.released,(by rw [← hJoinPc]; exact joined.checkpoint),joined.recorded,joined.remaining,
      joined.localSteps⟩
  have hOrigin n (hn : n ∈ [mode.alphaReg,7257,7258]) :
      n ∈ repeatedProbabilityRetained mode := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> cases mode <;> decide
  let ops := hOperands g hw
  let out : RepeatedProbabilityJoinCursor l X g mode (warp g) (weights g) (old g) (alpha g)
      (phase g) :=
    ⟨values g,hJoined,
      hValue g hw 7257 ((hKeep g hw _ (hOrigin _ (by simp))).trans ops.oldMass),
      (congrArg (valFloat .f32) (hValue g hw mode.alphaReg
        ((hKeep g hw _ (hOrigin _ (by simp))).trans ops.coefficient))).trans ops.alphaValue,
      hValue g hw 7258 ((hKeep g hw _ (hOrigin _ (by simp))).trans ops.phaseWord),
      ops.phaseBound,
      fun n hn => hValue g hw n ((hWeights g hw).scalar n hn),
      fun n hn => hValue g hw n ((hWeights g hw).packed n hn)⟩
  have hHere : u.pos = (input g hw).pos+delay+9 := by
    rw [hUPos,hBarPos g hw]
    change (tail g hw).pos+1+1 = _
    rw [hPos g hw]
  have hEnd : joined.ending = (input g hw).ending :=
    hJoinEnding.trans (hUEnd.trans ((hBarEnding g hw).trans (hEnding g hw)))
  refine ⟨leader,out,hStores g hw,hCredit g hw,?_,?_⟩
  · intro hLead
    have he' := hTailCredit (by simp [chosen,hLead])
    have hStage : stageOf (warp g) = stage := ops.stageIndex
    change Thread.Scores.ProbabilityCredit l X (g,u.pos) (g/l.block) (stageOf (warp g)) 1 at he'
    simpa only [hHere,hStage] using he'
  · have hPostPos : (input g hw).pos+delay+8 = (post g hw).pos := by
      have := hUPos
      omega
    refine ⟨hEnd,?_,?_,⟨inst,by rw [hPostPos]; exact he⟩,?_,?_⟩
    · intro n hn
      obtain ⟨v,hV⟩ := ops.continuation n hn
      have hRetained : n ∈ repeatedProbabilityRetained mode :=
        List.mem_append_right _ (Repeated.continuationRegs_mem hn)
      exact hV.trans (congrArg some (hValue g hw n ((hKeep g hw n hRetained).trans hV)).symm)
    · -- the tail window, the warp barrier, the election and the optional tail credit
      have hTailPos : (tail g hw).pos = (input g hw).pos+delay+7 := hPos g hw
      have hNoticeTail : ((X.tr g).take (tail g hw).pos).countP Thread.Scores.publishesStats =
          notices g := by
        rw [hTailPos]
        exact (repeatedProbabilityCount (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
          mode stage (weights g) (hStores g hw) (hDelayed g hw) (hWait g hw) (hCredit g hw)
          (hTailWait g hw)).trans (hNotices g hw)
      have hCreditTail : ((X.tr g).take (tail g hw).pos).countP Thread.Scores.creditAcquired =
          credits g := by
        rw [hTailPos]
        exact (repeatedProbabilityCount (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
          mode stage (weights g) (hStores g hw) (hDelayed g hw) (hWait g hw) (hCredit g hw)
          (hTailWait g hw)).trans (hCredits g hw)
      have hScoreTail : ((X.tr g).take (tail g hw).pos).countP scoreAcquired =
          scorePolls g := by
        rw [hTailPos]
        exact (repeatedProbabilityCount (fun _ _ => rfl) (fun _ _ _ _ _ _ => rfl)
          mode stage (weights g) (hStores g hw) (hDelayed g hw) (hWait g hw) (hCredit g hw)
          (hTailWait g hw)).trans (hScores g hw)
      have hTailCounts : SoftmaxCounts X g (tail g hw).pos (ordinal+delay+6) bars elects
          (notices g) (credits g) (scorePolls g) :=
        ⟨hTc g hw,(hTailRanks g hw).1,(hTailRanks g hw).2,hNoticeTail,hCreditTail,hScoreTail⟩
      obtain ⟨barPc,hBarEv⟩ := hBarGet g hw
      have hPostCounts : SoftmaxCounts X g (post g hw).pos (ordinal+delay+6) (bars+1) elects
          (notices g) (credits g) (scorePolls g) := by
        have e := hBarPos g hw
        refine ⟨?_,hNextRank g hw,?_,?_,?_,?_⟩ <;> rw [e]
        · exact (countP_take_succ_false hBarEv rfl).trans hTailCounts.1
        · exact (countP_take_succ_false hBarEv rfl).trans hTailCounts.2.2.1
        · exact (countP_take_succ_false hBarEv rfl).trans hTailCounts.2.2.2.1
        · exact (countP_take_succ_false hBarEv rfl).trans hTailCounts.2.2.2.2.1
        · exact (countP_take_succ_false hBarEv rfl).trans hTailCounts.2.2.2.2.2
      have hElectEv := he
      unfold Execution.Elect at hElectEv
      have hUCounts : SoftmaxCounts X g u.pos (ordinal+delay+6) (bars+1) (elects+1)
          (notices g) (credits g) (scorePolls g) := by
        refine ⟨?_,?_,hURank,?_,?_,?_⟩ <;> rw [hUPos]
        · exact (countP_take_succ_false hElectEv rfl).trans hPostCounts.1
        · exact (countP_take_succ_false (p := Execution.isWarpBar) hElectEv rfl).trans
            hPostCounts.2.1
        · exact (countP_take_succ_false hElectEv rfl).trans hPostCounts.2.2.2.1
        · exact (countP_take_succ_false hElectEv rfl).trans hPostCounts.2.2.2.2.1
        · exact (countP_take_succ_false hElectEv rfl).trans hPostCounts.2.2.2.2.2
      change SoftmaxCounts X g joined.pos _ _ _ _ _ _
      rw [hJoinPos]
      by_cases hChosen : chosen = true
      · rw [ite_eq_left hChosen]
        obtain ⟨cpc,hCreditEv⟩ := hTailCredit hChosen
        exact SoftmaxCounts.ofSilent (n := 1) (fun k hk => by
          obtain rfl : k = 0 := by omega
          exact ⟨_,hCreditEv,rfl,rfl,rfl,rfl,rfl,rfl⟩) hUCounts
      · rw [ite_eq_right hChosen]
        exact hUCounts
    · have hp' : payload.pos = (input g hw).pos+delay+9 := hHere
      change _ ≤ joined.pos
      rw [hJoinPos,hp']
      by_cases hc : chosen = true
      · rw [ite_eq_left hc]; omega
      · rw [ite_eq_right hc]
    · intro hLead
      have hp' : payload.pos = (input g hw).pos+delay+9 := hHere
      have hChosen : chosen = true := by simp [chosen,hLead]
      change _ < joined.pos
      rw [hJoinPos,hp',ite_eq_left hChosen]
      omega

end PTX.Kernels.TmlFa4Fwd.Softmax
