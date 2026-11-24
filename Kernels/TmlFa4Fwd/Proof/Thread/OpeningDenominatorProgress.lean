-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningMassOfAck
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningLoopRegisters
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLaneRegister
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalIssueProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

private theorem maskedOfNoScoreMaximum (scores : Nat → Option ℝ) {columns : List Nat}
    (h : scoreMax scores columns = none) : ∀ j ∈ columns, scores j = none := by
  induction columns with
  | nil => simp
  | cons col columns ih =>
    have hh : maxScore (scores col) (scoreMax scores columns) = none := h
    cases hs : scores col with
    | none =>
      rw [hs,maxScore] at hh
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hm
      · exact hs
      · exact ih hh j hm
    | some value =>
      cases hRest : scoreMax scores columns <;> simp [hs,hRest,maxScore] at hh

private theorem openingDenominatorValid (scale reference : ℝ) (scores : Nat → Option ℝ) :
    DenominatorValid (∑ i ∈ Finset.range 128, openingPackedWeight scale reference scores i)
      (scoreMax scores (List.range 128)) := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    cases h : affineScore scale (-reference) (scores i) with
    | none => simp [openingPackedWeight,h]
    | some x => exact (by simpa [openingPackedWeight,h] using
        (Real.rpow_nonneg (show 0 ≤ (2 : ℝ) by norm_num) x))
  · intro hs
    cases h : scoreMax scores (List.range 128) with
    | some value => exact ⟨value,rfl⟩
    | none =>
      have hZero : (∑ i ∈ Finset.range 128, openingPackedWeight scale reference scores i) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hMask := maskedOfNoScoreMaximum scores h j
          (List.mem_range.mpr (Finset.mem_range.mp hj))
        simp [openingPackedWeight,affineScore,hMask]
      rw [hZero] at hs
      exact (lt_irrefl 0 hs).elim

/-- The first denominator and loop geometry at the actual checkpoint of an active lane. -/
structure OpeningDenominatorCursor (p : Params) (l : Launch) (X : Execution)
    (g blocks cap past : Nat) where
  maximum : Option ℝ
  sum : ℝ
  valid : DenominatorValid sum maximum
  cursor : PTX.Kernels.TmlFa4Fwd.Correction.OpeningTripCursor l X g 5006
    (((1228,b32 cap) :: firstLoopStable blocks past maximum sum) ++
      openingDenominatorRegisters p l g)

  tensors : ((X.tr g).take cursor.pos).countP isTcColl = 11

/-- An actual opening acknowledgement leads to the loop decision with the retained score,
denominator, and ABI registers, right after the acknowledgement event. The proof also applies
to masked rows and suspended lanes. -/
theorem OpeningProbabilityAck.denominatorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (ack : OpeningProbabilityAck l X g) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
    let past := p.kLength batch-p.qLength batch+256*coords.1
    ∃ c : OpeningDenominatorCursor p l X g blocks cap past, c.cursor.pos = ack.index+1 := by
  let coords := Epilogue.assignedCoordinates p batch (g/l.block)
  let blocks := Mma.trips p batch coords.1
  let cap := blocks-stageGeometryBlocks p batch coords.1 stage+10
  let past := p.kLength batch-p.qLength batch+256*coords.1
  obtain ⟨_,_,⟨arrival⟩,hReleased⟩ :=
    Progress.openingSoftmaxBiasRendezvousOfAllStages hp hMax hFrame hg stage hRole hb hLo hHi
  obtain ⟨c,hLoop,hMaximum,_,hSetup⟩ :=
    arrival.statisticsWithScoresAndRegistersOfMaximal hp hMax hFrame hg hb hLo hHi
      (hReleased.imp_right (fun ⟨Y,hY,hTrace,_,hReady⟩ => ⟨Y,hY,hTrace,hReady⟩))
  have hRelease (hEnd : c.index+1 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
    have hj : c.index = (X.tr g).length-1 := by omega
    exact Progress.openingStatisticsReleasedHistory hp hMax hFrame hg stage hRole hb hLo hHi
      (hj ▸ c.published)
  obtain ⟨early,_,hNumbers,hWeights,hCarry,hResidents,hNegative⟩ :=
    c.probabilityWaitWithWeightsAndRegistersOfMaximal hp hg hRelease
  have hBound : early.statistics.index+2 ≤ (X.tr g).length := by
    have he : X.get (g,early.statistics.index+1) = some ⟨4826,.tc .waitLd⟩ := early.waited
    exact len_of_get he
  obtain ⟨v,hV,hLocal,_,hKeeps⟩ := ack.firstMass early hBound hWeights
  have hKeep r (hr : r ∈ firstTransitionRegs) :=
    (hKeeps r (List.mem_append_right _ hr)).trans (hCarry r hr)
  let maxWord := scoreMax c.scores (List.range 128)
  let sum := ∑ i ∈ Finset.range 128, early.values i
  obtain ⟨hPast,hBlocks,hCap,hLast,_⟩ := hLoop
  have hState : Holds v.regs ((1228,b32 cap) :: firstLoopStable blocks past maxWord sum) :=
    ⟨(hKeep 1228 (by decide)).trans hCap,(hKeep 1226 (by decide)).trans hBlocks,
      (hKeep 1229 (by decide)).trans hLast,(hKeep 1225 (by decide)).trans hPast,
      (hKeep 7256 (by decide)).trans hMaximum,hV.2.2.2.2.1,trivial⟩
  obtain ⟨hWarp,hBase,hBar,_⟩ := hSetup
  have hAbi : Holds v.regs (openingDenominatorRegisters p l g) :=
    ⟨(hKeeps 1062 (by decide)).trans ((hResidents 1062 (by decide)).trans hWarp),
      (hKeeps 2535 (by decide)).trans ((hResidents 2535 (by decide)).trans hBase),
      (hKeeps 5127 (by decide)).trans ((hResidents 5127 (by decide)).trans hBar),
      (hKeeps 7132 (by decide)).trans ((hResidents 7132 (by decide)).trans c.ready.2.2.2.2.2.1),
      (hKeeps 1230 (by decide)).trans hNegative,trivial⟩
  have hValid : DenominatorValid sum maxWord := by
    dsimp only [sum,maxWord]
    rw [hNumbers]
    exact openingDenominatorValid _ _ c.scores
  exact ⟨⟨maxWord,sum,hValid,⟨ack.index+1,ack.before,v,ack.ending,Nat.succ_pos _,ack.bounded,
    ack.released,hV.mono ((holds_append _ _ _).mpr ⟨hState,hAbi⟩),ack.recorded,ack.continuing,
    ack.localSteps.trans hLocal⟩,ack.tensors⟩,rfl⟩

/-- The opening denominator takes the actual branch for the remaining visit schedule. -/
theorem OpeningDenominatorCursor.enterLoops {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g blocks cap past : Nat}
    (c : OpeningDenominatorCursor p l X g blocks cap past)
    (hBlocks : 0 < blocks) (hSigned : blocks < 2^31) (hCap : 0 < cap)
    (hCapSigned : cap < 2^31) (hPast : past+256 < 2^31) :
    let split := firstPlainSplit blocks cap
    let biased := firstBiasedRepeats blocks cap
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) c.cursor.ready u ∧
      (if biased = 0 then
        if split = 0 then
          At u 7605 ((1491,b32 split)::firstLoopChoiceFacts blocks split past c.maximum c.sum)
        else At u 6661 (firstPlainFacts p blocks split past c.maximum c.sum)
       else At u 5032 (firstBiasedFacts blocks split past c.maximum c.sum)) ∧
      Holds u.regs (openingDenominatorRegisters p l g) := by
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  obtain ⟨hState,hAbi⟩ := (holds_append ..).mp c.cursor.checkpoint.2.2.2.2
  obtain ⟨u,hLocal,hu⟩ := firstLoopEntryLocal (l := l) (g := g) blocks cap past c.maximum c.sum
    hBlocks hSigned hCap hCapSigned hPast (c.cursor.checkpoint.mono hState)
  by_cases hZero : biased = 0
  · have hu' : At u 6654 (firstLoopChoiceFacts blocks split past c.maximum c.sum) := by
      simpa only [show firstBiasedRepeats blocks cap = 0 from hZero,ite_true] using hu
    have hSplit : split < blocks := by unfold split firstPlainSplit; omega
    obtain ⟨v,hNext,hv⟩ := firstPlainEntryLocal hp (g := g) blocks split past c.maximum c.sum
      hSigned hSplit hu'
    have hPath := hLocal.trans hNext
    exact ⟨v,hPath,by
      simpa only [show firstBiasedRepeats blocks cap = 0 from hZero,ite_true] using hv,
      openingLoopRegistersLocal (.inl c.cursor.checkpoint.1) hAbi hPath⟩
  · exact ⟨u,hLocal,by
      simpa only [hZero,show firstBiasedRepeats blocks cap ≠ 0 from hZero,ite_false] using hu,
      openingLoopRegistersLocal (.inl c.cursor.checkpoint.1) hAbi hLocal⟩

/-- With a single visit, the actual opening denominator goes straight to the terminal
stores and final publication. Masked lanes take the same publishing path. -/
theorem OpeningDenominatorCursor.publishSingleVisitAtCursor {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {g cap past : Nat} (hg : g < l.threads)
    (hw : Prologue.warpIndex l g < 8) (hCap : 0 < cap) (hCapSigned : cap < 2^31)
    (hPast : past+256 < 2^31) (c : OpeningDenominatorCursor p l X g 1 cap past) :
    let warp : Fin 8 := ⟨Prologue.warpIndex l g,hw⟩
    Thread.Scores.Publishes X (g,c.cursor.pos+2) .final ∧
      X.Writes (g,c.cursor.pos) (statsAcc l g warp 2) (fl c.sum).toBytes ∧
      X.Writes (g,c.cursor.pos+1) (statsAcc l g warp 3) (scoreValue c.maximum).toBytes := by
  let warp : Fin 8 := ⟨Prologue.warpIndex l g,hw⟩
  have hBiased : firstBiasedRepeats 1 cap = 0 := by unfold firstBiasedRepeats; omega
  have hPlain : firstPlainSplit 1 cap = 0 := by unfold firstPlainSplit; omega
  obtain ⟨u,hLocal,hu,hAbi⟩ := c.enterLoops hp (by decide) (by decide) hCap hCapSigned hPast
  have hState : At u 7605 ((1491,b32 0)::firstLoopChoiceFacts 1 0 past c.maximum c.sum) := by
    simpa only [hBiased,hPlain,ite_true] using hu
  have hPath := c.cursor.localSteps.trans hLocal
  have hLane := laneRegisterOfMaximalCursor hp hMax hCuQ hg hw
    (by rw [hState.1]; decide) (by rw [hState.1]; decide) c.cursor.bounded c.cursor.recorded hPath
  let F := [(1215,b32 (laneOf l g)),(1062,b32 warp.val),(2535,b32 l.sharedBase),
    (7257,fl c.sum),(7256,scoreValue c.maximum),(5127,b32 (3+warp.val))]
  have hFrame : Holds u.regs F := by
    refine ⟨hLane,hAbi.1,hAbi.2.1,?_,?_,hAbi.2.2.1,trivial⟩
    · exact holds_mem hState.2.2.2.2
        (by simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable])
    · exact holds_mem hState.2.2.2.2
        (by simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable])
  let terminal : PTX.Kernels.TmlFa4Fwd.Correction.OpeningTripCursor l X g 7605 F :=
    ⟨c.cursor.pos,c.cursor.before,u,c.cursor.ending,c.cursor.positive,c.cursor.bounded,
      c.cursor.released,hState.mono hFrame,c.cursor.recorded,c.cursor.remaining,hPath⟩
  have hWord : (scoreValue c.maximum).bytes = 4 := by cases c.maximum <;> rfl
  obtain ⟨hSum,hMaxWord,hPub⟩ := terminalStatisticsPublicationOfMaximal hp hMax hg warp rfl
    rfl hWord terminal
  exact ⟨hPub,hSum,hMaxWord⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
