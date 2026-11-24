-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.PlainDenominatorVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedDenominatorIteration
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecordedSoftmaxRowPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.ReachedSoftmaxHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatisticsEarlyRank
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningLoopRegisters
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorOfComplete
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedProbabilityScoreCount
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopOrdinal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Numeric Prologue Epilogue Thread Thread.Scores
open Protocol

noncomputable section

/-- The launch geometry and actual terminal event of the softmax lane under replay. -/
structure NumericalRow (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  warp : Fin 8
  lane : warp.val = warpIndex l g
  validBatch : batch < p.batch
  lower : tilePrefix p batch*p.heads ≤ g/l.block
  upper : g/l.block < tilePrefix p (batch+1)*p.heads
  live : let co := assignedCoordinates p batch (g/l.block)
    256*co.1+128*(warpIndex l g/4)+(g%l.block)%128 < p.qLength batch
  last : Nat
  exitSite : Nat
  exit : X.get (g,last) = some ⟨exitSite,.exit⟩

namespace NumericalRow

variable {p : Params} {l : Launch} {X : Execution} {g batch : Nat}

def stage (row : NumericalRow p l X g batch) : Fin 2 := stageOf row.warp

theorem stageIndex (row : NumericalRow p l X g batch) :
    warpIndex l g/4 = row.stage.val := by rw [← row.lane]; rfl

end NumericalRow

/-- The numerical state after the recorded probability tiles of the lane. -/
structure NumericalCursor {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    (row : NumericalRow p l X g batch) where
  visited : Nat
  positive : 0 < visited
  refs : Nat → Option ℝ
  sums : Nat → ℝ
  maximum : Option ℝ
  reference : refs (visited-1) = maximum.map (abiFloat p.scaleLog2Bits * ·)
  phase : Bool
  scorePhase : Bool
  index : Nat
  state : TState
  recorded : TraceReach kernel Assumptions.all l g {} ((X.tr g).take index) state
  run : Run kernel Assumptions.all l g state ((X.tr g).drop index) none
  ordinal : probabilityOrdinal l X (g/l.block) row.stage 0 (g,index) = visited
  values : let co := assignedCoordinates p batch (g/l.block)
    RecordedSoftmaxRowPrefix p l X g batch co.2 (256*co.1+128*row.stage.val+(g%l.block)%128)
      row.stage (Mma.trips p batch co.1) visited refs sums

/-- The replay has consumed all scheduled scores and reached the
actual terminal numerical state. -/
def NumericalRow.Replayed {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    (row : NumericalRow p l X g batch) : Prop :=
  let co := assignedCoordinates p batch (g/l.block)
  let blocks := Mma.trips p batch co.1
  ∃ refs sums,
    RecordedSoftmaxRowPrefix p l X g batch co.2 (256*co.1+128*row.stage.val+(g%l.block)%128)
      row.stage blocks blocks refs sums ∧
    Thread.Correction.ReachedSoftmaxRowDrain p l X g (refs (blocks-1)) (sums (blocks-1))

private theorem finishNumericalCursor {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    {row : NumericalRow p l X g batch} (cur : NumericalCursor row)
    (hVisits : cur.visited = Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hPc : cur.state.pc = 7605)
    (hSum : cur.state.regs 7257 = some (fl (cur.sums (cur.visited-1))))
    (hMax : cur.state.regs 7256 = some (scoreValue cur.maximum)) : row.Replayed := by
  have hDrain := Thread.Correction.ReachedSoftmaxRowDrain.ofRecorded
    cur.reference hPc hSum hMax cur.run
  have hPrefix := cur.values
  rw [hVisits] at hPrefix hDrain
  exact ⟨cur.refs,cur.sums,hPrefix,hDrain⟩

private def plainHeadFrame {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    {row : NumericalRow p l X g batch} (cur : NumericalCursor row) (word : Nat) :
    List (Nat × Value) :=
  (1062,b32 row.warp.val)::(2535,b32 l.sharedBase)::(7253,b32 cur.scorePhase.toNat)::
    plainIterationInputs p row.warp cur.maximum (cur.sums (cur.visited-1)) cur.phase word

private theorem plainHeadOfLoopFacts {p : Params} {l : Launch} {X : Execution}
    {g batch : Nat} {row : NumericalRow p l X g batch} (cur : NumericalCursor row)
    (blocks split past : Nat)
    (hc : At cur.state 6661 (plainLoopFacts p blocks split past cur.maximum
      (cur.sums (cur.visited-1)) cur.phase cur.scorePhase))
    (hr : Holds cur.state.regs (openingDenominatorRegisters p l g)) :
    At cur.state 6661 (plainHeadFrame cur (2^32-split)) := by
  obtain ⟨hWarp,hBase,hStats,_,hNeg,_⟩ := hr
  rw [← row.lane] at hWarp hStats
  have hGet (x : Nat × Value)
      (hx : x ∈ plainLoopFacts p blocks split past cur.maximum
        (cur.sums (cur.visited-1)) cur.phase cur.scorePhase) := holds_mem hc.2.2.2.2 hx
  exact hc.mono ⟨hWarp,hBase,
    hGet (7253,b32 cur.scorePhase.toNat) (by simp [plainLoopFacts,loopChoiceFacts]),
    hGet (7255,scoreValue cur.maximum) (by simp [plainLoopFacts]),
    hGet (7257,fl (cur.sums (cur.visited-1))) (by
      simp [plainLoopFacts,loopChoiceFacts,firstLoopStable]),
    hGet (7258,b32 cur.phase.toNat) (by simp [plainLoopFacts,loopChoiceFacts]),
    hStats,hNeg,hGet (7133,b32 p.scaleLog2Bits) (by simp [plainLoopFacts]),
    hGet (8692,joinValue (b32 p.scaleLog2Bits) (b32 p.scaleLog2Bits)) (by simp [plainLoopFacts]),
    hGet (7254,b32 (2^32-split)) (by simp [plainLoopFacts]),trivial⟩

/-- The ordinary loop drains its exact remaining visits, from a genuine observed head. -/
private theorem replayPlainNumericalLoop {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (row : NumericalRow p l X g batch) (cur : NumericalCursor row) (word : Nat)
    (hWord : word < 2^32)
    (hRemaining : cur.visited+scoreLoopDistance .plain word =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (ht : At cur.state 6661 (plainHeadFrame cur word)) : row.Replayed := by
  obtain ⟨u,endPos,storePos,candidate,mass,hBefore,hEnd,hSum,hStore,hEvents,hProb,hu,hTail,
      hPath,_,hStoreRank,hNewRank⟩ :=
    plainDenominatorVisitOfHeadWithPath hp hX hFrame row.warp row.lane cur.maximum cur.phase
      cur.scorePhase word hWord cur.refs cur.sums cur.values.recurrence cur.positive
      cur.reference cur.ordinal ht cur.run row.exit row.validBatch row.lower row.upper row.live
  let max := chosenReference (abiFloat p.scaleLog2Bits) cur.maximum candidate
  let ref := max.map (abiFloat p.scaleLog2Bits * ·)
  let refs := Function.update cur.refs cur.visited ref
  let sums := Function.update cur.sums cur.visited mass
  let nextWord := (word+1)%2^32
  have hEndAfter : cur.index ≤ endPos := by omega
  have hPrefix := cur.recorded.append hPath
  rw [← List.take_add,Nat.add_sub_of_le hEndAfter] at hPrefix
  have hStoreEvent : StatisticsStore X (g,storePos) (rescaleStore false)
      (statsAcc l g row.warp 1) (alphaWord (abiFloat p.scaleLog2Bits) cur.maximum
        candidate).toBytes :=
    hStore
  have hStats := (rescaleStoreNoticeOfEarlyCredits hp hX (stage := row.stage) row.stageIndex
    hStoreEvent).trans
    hStoreRank
  let next : NumericalCursor row := {
    visited := cur.visited+1
    positive := by omega
    refs, sums
    maximum := max
    reference := by simp [refs,ref]
    phase := !cur.phase
    scorePhase := !cur.scorePhase
    index := endPos
    state := u
    recorded := hPrefix
    run := hTail
    ordinal := hNewRank
    values := cur.values.extendWithAlpha cur.positive cur.maximum candidate mass false cur.reference
      hSum hProb hStoreEvent hStats
  }
  change At u (if nextWord ≠ 0 then 6661 else 7605)
    ([(7254,b32 nextWord),(7255,scoreValue max),(7256,scoreValue max),(7257,fl mass),
      (7258,b32 (!cur.phase).toNat),(7253,b32 (!cur.scorePhase).toNat)]) at hu
  obtain ⟨hNext,hMaxPrior,hMax,hMass,hPhase,hScore,_⟩ := hu.2.2.2.2
  by_cases hContinue : nextWord ≠ 0
  · have hPc : u.pc = 6661 := by simpa only [ite_eq_left hContinue] using hu.1
    have hKeep := scoreTraceKeepsResidents .plain hPath ht.1.ge
      (by rw [hPc]; decide) (by rw [ht.2.1]; decide)
    obtain ⟨hWarp,hBase,_,_,_,_,hBar,hNeg,hBits,hPair,_,_⟩ := ht.2.2.2.2
    have hNextHead : At next.state 6661 (plainHeadFrame next nextWord) := by
      refine ⟨hPc,hu.2.1,hu.2.2.1,hu.2.2.2.1,?_⟩
      exact ⟨(hKeep 1062 (by decide)).trans hWarp,(hKeep 2535 (by decide)).trans hBase,hScore,
        hMaxPrior,by simpa [next,sums] using hMass,hPhase,
        (hKeep 5127 (by decide)).trans hBar,(hKeep 1230 (by decide)).trans hNeg,
        (hKeep 7133 (by decide)).trans hBits,(hKeep 8692 (by decide)).trans hPair,hNext,trivial⟩
    have hDistance : scoreLoopDistance .plain nextWord+1 = scoreLoopDistance .plain word :=
      scoreLoopDistance_step .plain hWord hContinue
    exact replayPlainNumericalLoop hp hX hFrame row next nextWord
      (Nat.mod_lt _ (by decide)) (by change cur.visited+1+_ = _; omega) hNextHead
  · have hExitWord : nextWord = (scoreLoopSite .plain).sentinel := Decidable.not_not.mp hContinue
    have hOne := distanceOnExit .plain hWord hExitWord
    have hVisits : next.visited = Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 :=
      by change cur.visited+1 = _; omega
    have hPc : u.pc = 7605 := by simpa [hExitWord,scoreLoopSite] using hu.1
    exact finishNumericalCursor next hVisits hPc (by simpa [next,sums] using hMass) hMax
termination_by scoreLoopDistance .plain word
decreasing_by
  have hDistance := scoreLoopDistance_step .plain hWord hContinue
  exact Nat.lt_of_succ_le hDistance.le

private def biasedGeometry (blocks split past : Nat) : List (Nat × Value) :=
  [(1360,b32 (past/128)),(1359,b32 split),(1226,b32 blocks),(1229,b32 (blocks-1)),
    (1225,b32 (past+256))]

private def biasedHeadFrame {p : Params} {l : Launch} {X : Execution} {g batch : Nat}
    {row : NumericalRow p l X g batch} (cur : NumericalCursor row) (biasPhase : Bool)
    (word block floor : Nat) : List (Nat × Value) :=
  [(7249,b32 block),(7251,scoreValue cur.maximum),(7257,fl (cur.sums (cur.visited-1))),
    (1361,b32 floor),(7258,b32 cur.phase.toNat),(1062,b32 row.warp.val),(2535,b32 l.sharedBase),
    (5127,b32 (3+row.warp.val)),(1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits),
    (7250,b32 biasPhase.toNat),(7253,b32 cur.scorePhase.toNat),(7248,b32 word)]

private theorem replayAfterBiased {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (row : NumericalRow p l X g batch) (cur : NumericalCursor row)
    (split past : Nat)
    (hBlocks : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2^31)
    (hSplit : split < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hVisited : cur.visited+split = Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (ht : At cur.state 6654 (loopChoiceFacts
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) split past cur.maximum
      (cur.sums (cur.visited-1)) cur.phase cur.scorePhase))
    (hRegs : Holds cur.state.regs (openingDenominatorRegisters p l g)) : row.Replayed := by
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  obtain ⟨u,hLocal,hu⟩ := plainLoopEntryLocal hp (g := g) blocks split past cur.maximum
    (cur.sums (cur.visited-1)) cur.phase cur.scorePhase hBlocks hSplit ht
  have hPrefix := cur.recorded.append (TraceReach.of_local hLocal)
  simp only [List.append_nil] at hPrefix
  let next : NumericalCursor row :=
    {cur with state := u, recorded := hPrefix, run := cur.run.after_local hLocal}
  have hValues := openingLoopRegistersLocal (.inr ht.1) hRegs hLocal
  by_cases hZero : split = 0
  · rw [ite_eq_left hZero] at hu
    have hVisits : next.visited = blocks := by change cur.visited = blocks; omega
    refine finishNumericalCursor next hVisits hu.1 ?_ ?_
    · change u.regs 7257 = some (fl (cur.sums (cur.visited-1)))
      exact holds_mem hu.2.2.2.2 (by simp [loopChoiceFacts,firstLoopStable])
    · change u.regs 7256 = some (scoreValue cur.maximum)
      exact holds_mem hu.2.2.2.2 (by simp [loopChoiceFacts,firstLoopStable])
  · rw [ite_eq_right hZero] at hu
    have hDistance := initialPlainDistance (Nat.pos_of_ne_zero hZero)
      (by omega : split < 2^31)
    have hAt := plainHeadOfLoopFacts next blocks split past hu hValues
    exact replayPlainNumericalLoop hp hX hFrame row next (2^32-split)
      (by omega) (by change cur.visited+_ = blocks; rw [hDistance]; exact hVisited) hAt

/-- The biased loop replays the remaining masked visits, then enters the actual
ordinary loop or final state with the same numerical row history. -/
private theorem replayBiasedNumericalLoop {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (row : NumericalRow p l X g batch) (cur : NumericalCursor row)
    (biasPhase : Bool) (word block floor split past : Nat)
    (hWord : word < 2^32) (hBlock : block < 2^32)
    (hBlocks : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2^31)
    (hSplit : split < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hRemaining : cur.visited+scoreLoopDistance .biased word+split =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (ht : At cur.state 5032 (biasedHeadFrame cur biasPhase word block floor ++
      biasedGeometry (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) split past)) :
    row.Replayed := by
  let blocks := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hFrames := (holds_append ..).mp ht.2.2.2.2
  have hLast := denominatorRunIndex_lt cur.run
  have hExitLen := X.exit_last hX (event_thread_lt hX row.exit) row.exit
  change row.last+1 = (X.tr g).length at hExitLen
  obtain ⟨u,endPos,storePos,candidate,mass,bar,hBefore,hEnd,hSum,hStore,hEvents,hu,hBar,hTail,
      hReach,hEarly,hStoreRank,hRank,hNewBlock⟩ :=
    biasedDenominatorVisitOfHeadWithPath hp hX hFrame row.warp row.lane cur.maximum cur.phase
      biasPhase cur.scorePhase word block floor hWord hBlock cur.refs cur.sums cur.values.recurrence
      cur.reference cur.ordinal (ht.mono hFrames.1) cur.recorded cur.run row.exit
      (by omega) row.validBatch row.lower row.upper row.live
  let max := chosenReference (abiFloat p.scaleLog2Bits) cur.maximum candidate
  let ref := max.map (abiFloat p.scaleLog2Bits * ·)
  let refs := Function.update cur.refs cur.visited ref
  let sums := Function.update cur.sums cur.visited mass
  let nextWord := (word+1)%2^32
  let nextBlock := (block+(2^32-1))%2^32
  have hStats := (rescaleStoreNoticeOfEarlyCredits hp hX (stage := row.stage) row.stageIndex
    hStore).trans
    hStoreRank
  have hPcChoice : u.pc = 5032 ∨ u.pc = 6654 := by
    have hPc := hu.1
    change u.pc = (if nextWord ≠ 2^32-1 then 5032 else 6654) at hPc
    split at hPc
    · exact .inl hPc
    · exact .inr hPc
  have hProb := biasedObservedProbabilityTileOfIteration hp hX row.stage row.stageIndex hStore
    hStats hReach hPcChoice hEarly hEvents hEnd hBar
  let next : NumericalCursor row := {
    visited := cur.visited+1
    positive := by omega
    refs, sums
    maximum := max
    reference := by simp [refs,ref]
    phase := !cur.phase
    scorePhase := !cur.scorePhase
    index := endPos
    state := u
    recorded := hReach
    run := hTail
    ordinal := hRank
    values := cur.values.extendWithAlpha cur.positive cur.maximum candidate mass true cur.reference
      hSum hProb hStore hStats
  }
  have hPath := betweenRecordedBiasedCheckpoints (by omega : cur.index < endPos)
    (denominatorRunIndex_lt hTail).le cur.recorded hReach
  have hKeep := scoreTraceKeepsResidents .biased hPath ht.1.ge
    (by rcases hPcChoice with h | h <;> rw [h] <;> decide) (by rw [ht.2.1]; decide)
  obtain ⟨_,_,_,hFloor,_,hWarp,hBase,hStatsReg,hNeg,hBits,_,_,_,_⟩ := hFrames.1
  obtain ⟨hPastTile,hSplitReg,hTrips,hBlocksReg,hPast,_⟩ := hFrames.2
  change At u (if nextWord ≠ 2^32-1 then 5032 else 6654)
    ([(7248,b32 nextWord),(7251,scoreValue max),(7256,scoreValue max),(7257,fl mass),
      (7258,b32 (!cur.phase).toNat),(7250,b32 (!biasPhase).toNat),(7253,b32
        (!cur.scorePhase).toNat)])
    at hu
  obtain ⟨hCount,hMaxPrior,hMax,hMass,hPhase,hBias,hScore,_⟩ := hu.2.2.2.2
  have hMass' : u.regs 7257 = some (fl (next.sums (next.visited-1))) := by
    simpa [next,sums] using hMass
  have hOld : Holds u.regs (biasedGeometry blocks split past) :=
    ⟨(hKeep 1360 (by decide)).trans hPastTile,(hKeep 1359 (by decide)).trans hSplitReg,
      (hKeep 1226 (by decide)).trans hTrips,(hKeep 1229 (by decide)).trans hBlocksReg,
      (hKeep 1225 (by decide)).trans hPast,trivial⟩
  by_cases hContinue : nextWord ≠ 2^32-1
  · have hPc : u.pc = 5032 := by simpa only [ite_eq_left hContinue] using hu.1
    have hHead : At next.state 5032 (biasedHeadFrame next (!biasPhase) nextWord nextBlock floor ++
        biasedGeometry blocks split past) := by
      refine ⟨hPc,hu.2.1,hu.2.2.1,hu.2.2.2.1,(holds_append ..).mpr ⟨?_,hOld⟩⟩
      exact ⟨hNewBlock,hMaxPrior,hMass',(hKeep 1361 (by decide)).trans hFloor,hPhase,
        (hKeep 1062 (by decide)).trans hWarp,(hKeep 2535 (by decide)).trans hBase,
        (hKeep 5127 (by decide)).trans hStatsReg,(hKeep 1230 (by decide)).trans hNeg,
        (hKeep 7132 (by decide)).trans hBits,hBias,hScore,hCount,trivial⟩
    have hDistance : scoreLoopDistance .biased nextWord+1 = scoreLoopDistance .biased word :=
      scoreLoopDistance_step .biased hWord hContinue
    exact replayBiasedNumericalLoop hp hX hFrame row next (!biasPhase) nextWord nextBlock floor
      split past (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hBlocks hSplit
      (by change cur.visited+1+_+split = blocks; omega) hHead
  · have hExitWord := Decidable.not_not.mp hContinue
    have hPc : u.pc = 6654 := by simpa [hExitWord] using hu.1
    have hOne := distanceOnExit .biased hWord hExitWord
    have hVisited : next.visited+split = blocks := by change cur.visited+1+split = blocks; omega
    obtain ⟨hTile,hSplit',hTrips',hBlocks',hPast',_⟩ := hOld
    have hAt : At next.state 6654
        (loopChoiceFacts blocks split past max (next.sums (next.visited-1)) next.phase
          next.scorePhase) :=
      ⟨hPc,hu.2.1,hu.2.2.1,hu.2.2.2.1,hTile,hSplit',hScore,hPhase,
        hTrips',hBlocks',hPast',hMax,hMass',trivial⟩
    have hRegs : Holds next.state.regs (openingDenominatorRegisters p l g) := by
      simp only [openingDenominatorRegisters,← row.lane]
      exact ⟨(hKeep 1062 (by decide)).trans hWarp,(hKeep 2535 (by decide)).trans hBase,
        (hKeep 5127 (by decide)).trans hStatsReg,(hKeep 7132 (by decide)).trans hBits,
        (hKeep 1230 (by decide)).trans hNeg,trivial⟩
    exact replayAfterBiased hp hX hFrame row next split past hBlocks hSplit hVisited hAt hRegs
termination_by scoreLoopDistance .biased word
decreasing_by
  have hDistance := scoreLoopDistance_step .biased hWord hContinue
  exact Nat.lt_of_succ_le hDistance.le



/-- Every live softmax lane in a complete execution gives its actual row history and drain. -/
theorem replayNumericalRowOfComplete {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hAllFrames : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hLive : let coords := assignedCoordinates p batch (g/l.block)
      stageRow coords.1 stage+g%l.block%128 < p.qLength batch) :
    let coords := assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let row := stageRow coords.1 stage+g%l.block%128
    ∃ refs sums,
      RecordedSoftmaxRowPrefix p l X g batch coords.2 row stage blocks blocks refs sums ∧
      Thread.Correction.ReachedSoftmaxRowDrain p l X g (refs (blocks-1)) (sums (blocks-1)) := by
  let coords := assignedCoordinates p batch (g/l.block)
  let tile := coords.1
  let blocks := Mma.trips p batch tile
  let cap := blocks-stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  let split := firstPlainSplit blocks cap
  let biased := firstBiasedRepeats blocks cap
  let lrow := 128*(2*tile+stage.val)+g%l.block%128
  let mx := scoreMax (fun c => maskedLogit p batch coords.2 lrow (visitKey blocks 0 c))
    (List.range 128)
  let ref := firstReference p batch coords.2 lrow blocks
  let mass := (2 : ℝ)^(-ref)*maskedBlockSum (p.keyCount batch lrow) blocks 0
    (weight p batch coords.2 lrow)
  obtain ⟨last,⟨pc,kind⟩,hExit,hKind⟩ := Thread.exitedOfComplete hX hDone hg
  change kind = .exit at hKind
  subst kind
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  let row : NumericalRow p l X g batch := {
    warp := ⟨warpIndex l g,hWarp⟩
    lane := rfl
    validBatch := hb
    lower := hLo
    upper := hHi
    live := by simpa only [hRole,stageRow] using hLive
    last := last
    exitSite := pc
    exit := hExit
  }
  have hStage : row.stage = stage := Fin.ext hRole
  have hRowFormula : lrow = stageRow tile stage+g%l.block%128 := by
    unfold lrow stageRow
    omega
  have hLive' : 128*(2*tile+stage.val)+g%l.block%128 < p.qLength batch := by
    change lrow < p.qLength batch
    rw [hRowFormula]
    exact hLive
  obtain ⟨hInitial,j,u,hReach,hRun,hCount,hAt,hRegs⟩ :=
    openingDenominatorHeadWithRegistersOfComplete hp hX hDone hAllFrames hg stage hRole
      hb hLo hHi hLive'
  have hExact : 256*coords.1+128*row.stage.val+g%l.block%128 = lrow := by
    rw [hStage]
    change 256*tile+128*stage.val+g%l.block%128 = 128*(2*tile+stage.val)+g%l.block%128
    omega
  have hInitial' : RecordedSoftmaxRowPrefix p l X g batch coords.2
      (256*coords.1+128*row.stage.val+g%l.block%128) row.stage blocks 1
      (fun _ => mx.map (abiFloat p.scaleLog2Bits * ·)) (fun _ => mass) := by
    rw [hExact,hStage]
    exact hInitial
  let cur : NumericalCursor row := {
    visited := 1
    positive := by decide
    refs := fun _ => mx.map (abiFloat p.scaleLog2Bits * ·)
    sums := fun _ => mass
    maximum := mx
    reference := rfl
    phase := true
    scorePhase := true
    index := j
    state := u
    recorded := hReach
    run := hRun
    ordinal := by rw [hStage]; exact hCount
    values := hInitial'
  }
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨hPositive,hUpper,_⟩ := Mma.trips_bounds hp hb hTile
  have hMaxLength := (hp.lengths batch hb).2.2
  change 0 < blocks at hPositive
  change blocks ≤ (p.kLength batch+127)/128 at hUpper
  have hb32 : blocks < 2^31 := by omega
  have hs : split < blocks := by unfold split firstPlainSplit; omega
  have hPartition : 1+biased+split = blocks := by unfold biased firstBiasedRepeats; omega
  have hRest : row.Replayed := by
    change (if biased = 0 then
      if split = 0 then At u 7605 ((1491,b32 split)::firstLoopChoiceFacts blocks split past mx mass)
      else At u 6661 (firstPlainFacts p blocks split past mx mass)
      else At u 5032 (firstBiasedFacts blocks split past mx mass)) at hAt
    by_cases hBias : biased = 0
    · rw [ite_eq_left hBias] at hAt
      by_cases hPlain : split = 0
      · rw [ite_eq_left hPlain] at hAt
        refine finishNumericalCursor cur (by change 1 = blocks; omega) hAt.1 ?_ ?_
        · change u.regs 7257 = some (fl mass)
          exact holds_mem hAt.2.2.2.2 (by
            simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable])
        · change u.regs 7256 = some (scoreValue mx)
          exact holds_mem hAt.2.2.2.2 (by
            simp [firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable])
      · rw [ite_eq_right hPlain] at hAt
        have hDist := initialPlainDistance (Nat.pos_of_ne_zero hPlain) (by omega : split < 2^31)
        have hHead := plainHeadOfLoopFacts cur blocks split past hAt hRegs
        exact replayPlainNumericalLoop hp hX (hAllFrames X hX) row cur _ (by omega)
          (by change 1+_ = blocks; omega) hHead
    · rw [ite_eq_right hBias] at hAt
      have hDist := initialBiasedDistance hb32 (by omega : split+1 < blocks)
      have hHead : At cur.state 5032
          (biasedHeadFrame cur true (2^32-(blocks-split)) (blocks-1) (past/128) ++
            biasedGeometry blocks split past) := by
        refine hAt.mono ((holds_append ..).mpr ⟨?_,?_⟩)
        · obtain ⟨hWarp,hBase,hStats,hBits,hNeg,_⟩ := hRegs
          have hGet (x : Nat × Value) (hm : x ∈ firstBiasedFacts blocks split past mx mass) :=
            holds_mem hAt.2.2.2.2 hm
          exact ⟨hGet (7249,b32 (blocks-1)) (by simp [firstBiasedFacts]),
            hGet (7251,scoreValue mx) (by simp [firstBiasedFacts]),
            hGet (7257,fl mass) (by
              simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]),
            hGet (1361,b32 (past/128)) (by simp [firstBiasedFacts]),
            hGet (7258,b32 1) (by simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts]),
            hWarp,hBase,hStats,hNeg,hBits,hGet (7250,b32 1) (by simp [firstBiasedFacts]),
            hGet (7253,b32 1) (by simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts]),
            hGet (7248,b32 (2^32-(blocks-split))) (by simp [firstBiasedFacts]),trivial⟩
        · have hGet (x : Nat × Value) (hm : x ∈ firstBiasedFacts blocks split past mx mass) :=
            holds_mem hAt.2.2.2.2 hm
          refine ⟨hGet (1360,b32 (past/128)) ?_,hGet (1359,b32 split) ?_,
            hGet (1226,b32 blocks) ?_,hGet (1229,b32 (blocks-1)) ?_,
            hGet (1225,b32 (past+256)) ?_,trivial⟩
          all_goals simp [firstBiasedFacts,firstLoopChoiceFacts,loopChoiceFacts,firstLoopStable]
      exact replayBiasedNumericalLoop hp hX (hAllFrames X hX) row cur true _ _ _ split past
        (by omega) (by omega) hb32 hs (by change 1+_+split = blocks; omega) hHead
  obtain ⟨refs,sums,hRecorded,hDrain⟩ := hRest
  rw [hExact,hStage,hRowFormula] at hRecorded
  exact ⟨refs,sums,hRecorded,hDrain⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
