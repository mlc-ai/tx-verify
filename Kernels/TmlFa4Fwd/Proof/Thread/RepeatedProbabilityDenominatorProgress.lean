-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailAlignment
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailJoin
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityTailAck
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- The live arithmetic carried into a repeated probability tail starts at the
actual affine state, including its old denominator and the published coefficient. -/
structure RepeatedTailOperands (l : Launch) (mode : Repeated) (stage : Fin 2)
    (s : TState) (warp : Fin 8) (old alpha : ℝ) (phase : Nat) where
  stageIndex : stageOf warp = stage
  abi : Holds s.regs (tailFrame l warp)
  oldMass : s.regs 7257 = some (fl old)
  alphaWord : Value
  coefficient : s.regs mode.alphaReg = some alphaWord
  alphaValue : valFloat .f32 alphaWord = .ok alpha
  phaseWord : s.regs 7258 = some (b32 phase)
  phaseBound : phase < 2
  continuation : ∀ n ∈ mode.continuationRegs, ∃ v, s.regs n = some v

private theorem tailScalarDefined {mode : Repeated} {s : TState} {weights : Nat → ℝ}
    (hWeights : RepeatedWeights mode s weights) (n : Nat)
    (hn : n ∈ mode.scalarInputs ++ mode.packedInputs) : ∃ v, s.regs n = some v := by
  rcases List.mem_append.mp hn with h | h
  · exact ⟨_,hWeights.scalar n h⟩
  · exact ⟨_,hWeights.packed n h⟩

private theorem repeatedTailFrameDefined {l : Launch} {mode : Repeated}
    {stage : Fin 2} {s u : TState} {warp : Fin 8} {old alpha : ℝ} {phase : Nat}
    (f : RepeatedTailOperands l mode stage s warp old alpha phase)
    (hKeep : ∀ n ∈ repeatedProbabilityRetained mode, u.regs n = s.regs n)
    {weights : Nat → ℝ} (hWeights : RepeatedWeights mode u weights) :
    (∀ n ∈ tailLiveWith mode.round true, ∃ v, u.regs n = some v) ∧
      Holds u.regs (tailFrame l warp) := by
  have hAbi (n : Nat) (hn : n ∈ [1062,2535,mode.alphaReg,7257,7258]) :
      n ∈ repeatedProbabilityRetained mode := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> cases mode <;> decide
  constructor
  · intro n hn
    have hn : n ∈ mode.sumLive ++ mode.continuationRegs := by cases mode <;> exact hn
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp (show n ∈ (mode.scalarInputs ++ mode.packedInputs) ++
        [mode.alphaReg,7257,7258] from hn) with hm | hm
      · exact tailScalarDefined hWeights n hm
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl
        · exact ⟨_,(hKeep _ (hAbi _ (by simp))).trans f.coefficient⟩
        · exact ⟨_,(hKeep _ (hAbi _ (by simp))).trans f.oldMass⟩
        · exact ⟨_,(hKeep _ (hAbi _ (by simp))).trans f.phaseWord⟩
    · obtain ⟨v,hv⟩ := f.continuation n hn
      exact ⟨v,(hKeep n (List.mem_append_right _ (Repeated.continuationRegs_mem hn))).trans hv⟩
  · exact ⟨(hKeep _ (hAbi _ (by simp))).trans f.abi.1,
      (hKeep _ (hAbi _ (by simp))).trans f.abi.2.1,trivial⟩

private theorem repeatedFrameHolds {l : Launch} {mode : Repeated} {t : TState} {warp : Fin 8}
    (values : Nat → Value) (hAbi : Holds t.regs (tailFrame l warp))
    (hValues : ∀ n ∈ tailLiveWith mode.round true, t.regs n = some (values n)) :
    Holds t.regs (tailCarryWith l warp mode.round (some values) true) := by
  refine ⟨hAbi.1,hAbi.2.1,?_⟩
  generalize h : tailLiveWith mode.round true = ns at hValues ⊢
  clear h
  induction ns with
  | nil => trivial
  | cons n ns ih =>
    exact ⟨hValues n (.head _),ih (fun r hr => hValues r (.tail _ hr))⟩

/-- The ready state after a repeated probability publication carries the exact
exponent vector, prior mass, rescale word, phase, and next-visit registers. -/
structure RepeatedProbabilityJoinCursor (l : Launch) (X : Execution) (g : Nat)
    (mode : Repeated) (warp : Fin 8) (weights : Nat → ℝ) (old alpha : ℝ) (phase : Nat) where
  values : Nat → Value
  cursor : OpeningTripCursor l X g ((signalSite mode.tailSignal).pc+1)
    (tailCarryWith l warp mode.round (some values) true)
  oldMass : values 7257 = fl old
  alphaValue : valFloat .f32 (values mode.alphaReg) = .ok alpha
  phaseWord : values 7258 = b32 phase
  phaseBound : phase < 2
  scalar : ∀ n ∈ mode.scalarInputs, values n =
    fl (weights (2*mode.packedInputs.length+mode.scalarInputs.idxOf n))
  packed : ∀ n ∈ mode.packedInputs, values n =
    .pair (fl (weights (2*mode.packedInputs.idxOf n)))
      (fl (weights (2*mode.packedInputs.idxOf n+1)))

private theorem sumLiveInTail {mode : Repeated} {n : Nat} (hn : n ∈ mode.sumLive) :
    n ∈ tailLiveWith mode.round true := by
  have h : n ∈ mode.sumLive ++ mode.continuationRegs := List.mem_append_left _ hn
  cases mode <;> exact h

private theorem tailFrameReg {l : Launch} {mode : Repeated} {warp : Fin 8}
    {t : TState} {vals : Nat → Value} {n : Nat}
    (hHold : Holds t.regs (tailCarryWith l warp mode.round (some vals) true))
    (hn : n ∈ mode.sumLive) : t.regs n = some (vals n) :=
  holds_mem hHold (.tail _ (.tail _ (mem_factsFrom (sumLiveInTail hn))))

/-- A matching actual correction credit makes the repeated denominator runnable. -/
theorem RepeatedProbabilityJoinCursor.denominatorWithPhaseOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    {mode : Repeated} {warp : Fin 8} {weights : Nat → ℝ} {old alpha : ℝ} {phase : Nat}
    (j : RepeatedProbabilityJoinCursor l X g mode warp weights old alpha phase)
    (hReady : OpeningPollReady X (waitLoc l g (stageOf warp) mode.correctionSite) phase) :
    let mass := old*alpha + ∑ i ∈ Finset.range 128, weights i
    ∃ index,
      ∃ u : OpeningTripCursor l X g mode.sumEnd [(7257,fl mass)],
        X.get (g,index) = some ⟨(waitSite mode.correctionSite).pc,
          .wait (waitLoc l g (stageOf warp) mode.correctionSite) phase true true .cta⟩ ∧
        u.pos = index+1 ∧ u.ending = j.cursor.ending ∧
        u.ready.regs 7258 = some (b32 phase) ∧
        ∀ n ∈ mode.continuationRegs, u.ready.regs n = some (j.values n) := by
  obtain ⟨index,entered,he,_,hPos,hEnding⟩ :=
    repeatedProbabilityTailAckOfMaximal hp hMax hg mode warp phase j.phaseBound j.values
      j.phaseWord true j.cursor hReady
  have hField (n : Nat) (hn : n ∈ mode.sumLive) :
      entered.ready.regs n = some (j.values n) := tailFrameReg entered.checkpoint.2.2.2.2 hn
  have hOld : entered.ready.regs 7257 = some (fl old) :=
    (hField _ (by simp [Repeated.sumLive])).trans (congrArg some j.oldMass)
  have hAlpha := hField mode.alphaReg (by simp [Repeated.sumLive])
  have hWeights : RepeatedWeights mode entered.ready weights := by
    constructor
    · intro n hn
      exact (hField n (List.mem_append_left _ (List.mem_append_left _ hn))).trans
        (congrArg some (j.scalar n hn))
    · intro n hn
      exact (hField n (List.mem_append_left _ (List.mem_append_right _ hn))).trans
        (congrArg some (j.packed n hn))
  obtain ⟨u,hUPos,hUEnd,hKeep⟩ :=
    repeatedDenominatorOfCursor mode weights old alpha entered hOld hAlpha j.alphaValue hWeights
  have hPhase : u.ready.regs 7258 = some (b32 phase) :=
    ((hKeep 7258 (by simp [sumContinuationRegs])).trans
      (hField 7258 (by simp [Repeated.sumLive]))).trans (congrArg some j.phaseWord)
  refine ⟨index,u,he,hUPos.trans hPos,hUEnd.trans hEnding,hPhase,?_⟩
  intro n hn
  have hLive : n ∈ tailLiveWith mode.round true := by
    have h : n ∈ mode.sumLive ++ mode.continuationRegs := List.mem_append_right _ hn
    cases mode <;> exact h
  have hContinuation : n ∈ sumContinuationRegs := by
    have hm := Repeated.continuationRegs_mem hn
    simp only [roundContinuationRegs,sumContinuationRegs,List.mem_cons,List.not_mem_nil,or_false]
      at hm ⊢
    tauto
  exact (hKeep n hContinuation).trans (holds_mem entered.checkpoint.2.2.2.2
    (.tail _ (.tail _ (mem_factsFrom hLive))))

theorem RepeatedProbabilityJoinCursor.denominatorOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    {mode : Repeated} {warp : Fin 8} {weights : Nat → ℝ} {old alpha : ℝ} {phase : Nat}
    (j : RepeatedProbabilityJoinCursor l X g mode warp weights old alpha phase)
    (hReady : OpeningPollReady X (waitLoc l g (stageOf warp) mode.correctionSite) phase) :
    let mass := old*alpha + ∑ i ∈ Finset.range 128, weights i
    ∃ index,
      ∃ u : OpeningTripCursor l X g mode.sumEnd [(7257,fl mass)],
        X.get (g,index) = some ⟨(waitSite mode.correctionSite).pc,
          .wait (waitLoc l g (stageOf warp) mode.correctionSite) phase true true .cta⟩ ∧
        u.pos = index+1 ∧ u.ending = j.cursor.ending ∧
        ∀ n ∈ mode.continuationRegs, u.ready.regs n = some (j.values n) := by
  obtain ⟨index,u,he,hPos,hEnd,_,hControl⟩ := j.denominatorWithPhaseOfMaximal hp hMax hg hReady
  exact ⟨index,u,he,hPos,hEnd,hControl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {lead : Nat} (mode : Repeated) (stage : Fin 2)
    (ordinal bars elects : Nat) (scores : Nat → Nat → Option ℝ) (reference : Nat → ℝ)
    (warp : Nat → Fin 8) (old alpha : Nat → ℝ) (phase : Nat → Nat) {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g mode.affineStart (F g))
    (hFrame : ∀ g (hw : SameWarp l lead g),
      RepeatedProbabilityShiftFrame p l mode g stage (input g hw).ready (scores g) (reference g))
    (hOperands : ∀ g (hw : SameWarp l lead g),
      RepeatedTailOperands l mode stage (input g hw).ready (warp g) (old g) (alpha g) (phase g))
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP isTcColl = ordinal)
    (hBar : ∀ g (hw : SameWarp l lead g), warpBars X g (input g hw).pos = bars)
    (hElect : ∀ g (hw : SameWarp l lead g), elections X g (input g hw).pos = elects)
include hp hMax mode stage ordinal bars elects scores reference warp old alpha phase input hFrame
    hOperands hRank hBar hElect

/-- The whole reached affine warp issues all four physical probability quarters,
elects the actual tail publisher, and retains the numerical frame at the correction join. -/
theorem warpRepeatedProbabilityJoinFromShiftWithControlOfMaximal :
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
          ∀ n ∈ mode.continuationRegs,
            (input g hw).ready.regs n = some (j.values n) := by
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
  obtain ⟨inst,leader,u,he,hUPos,hUEnd,_⟩ :=
    warpTailProbabilityElectionOfMaximal hp hMax mode.round elects post hElectionRank
      (fun g pair hm => (hFresh g pair hm).1) (fun g pair hm => (hFresh g pair hm).2) g hw
  let chosen := laneOf l g == leader.val
  let payload : OpeningTripCursor l X g (probabilityWaitPc mode.round true+3)
      ((tailElectPred mode.round,.pred chosen)::carried g) :=
    ⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,
      u.checkpoint.mono ⟨u.checkpoint.2.2.2.2.1,u.checkpoint.2.2.2.2.2.2⟩,
      u.recorded,u.remaining,u.localSteps⟩
  obtain ⟨joined,hTailCredit,_hJoinPos,hJoinEnding⟩ :=
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
  · refine ⟨hEnd,?_⟩
    intro n hn
    obtain ⟨v,hV⟩ := ops.continuation n hn
    have hRetained : n ∈ repeatedProbabilityRetained mode :=
      List.mem_append_right _ (Repeated.continuationRegs_mem hn)
    exact hV.trans (congrArg some (hValue g hw n ((hKeep g hw n hRetained).trans hV)).symm)

end PTX.Kernels.TmlFa4Fwd.Softmax
