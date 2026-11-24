-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityStoreOfCredit
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreLoadSources
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityStoreScoreOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityObservations
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Tcgen05.TcMmaACell
import Lemmas.Protocol.StagingHandoff
import Lemmas.Protocol.UnitGate
import Kernels.TmlFa4Fwd.Proof.Thread.TmemTailProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.TcMma Thread Thread.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma
open Prologue (warpIndex)

def probabilityProducer (l : Launch) (cta : Nat) (stage : Fin 2) (row : Nat) : Nat :=
  cta*l.block+128*stage.val+row

private theorem probabilityProducerGeometry {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (cta : Nat) (stage : Fin 2) {row : Nat}
    (hRow : row < 128) (hCta : cta < l.grid) :
    let g := probabilityProducer l cta stage row
    g < l.threads ∧ g/l.block = cta ∧
      warpIndex l g = 4*stage.val+row/32 ∧ laneBase l g+laneOf l g = row := by
  unfold probabilityProducer Launch.threads warpIndex laneBase laneOf
  rw [hp.block]
  have := stage.isLt
  dsimp only
  omega

/-- An observed probability credit causally precedes the MMA that resumes after its wait. -/
theorem probabilityCreditBeforeMma {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {credit wait mma : EvId} {stage packet : Fin 2}
    (hCredit : ProbabilityCredit l X credit (mma.1/l.block) stage packet)
    (hAcquire : MmaProbabilityAcquire l X mma stage packet wait)
    (hObserved : MbarObserved X (.thread credit) (.thread wait)) :
    baseCausality l X credit mma := by
  have hReceiver : ScoreAcquire X wait (probabilityObject l (mma.1/l.block) stage packet) :=
    hAcquire.event
  have hView := hReceiver.observes hObserved
  have hOwner := (probabilityCreditRole hp hX stage packet hCredit).1
  have hCr := hCredit
  obtain ⟨_,he⟩ := hCr
  obtain ⟨_,_,hf,_⟩ := hReceiver
  have hSame : SameCta l credit.1 wait.1 :=
    ⟨event_thread_lt hX he,event_thread_lt hX hf,
      hOwner.trans (congrArg (· / l.block) hAcquire.resume.1.1).symm⟩
  have hRelease : MbarRelease X credit (probabilityObject l (mma.1/l.block) stage packet) .cta :=
    ⟨0,1,hCredit⟩
  exact Staging.baseCausality_of_handoff hRelease hView
    (MbarRing.Unit.Gate.scopesMeet hSame .cta .cta) ⟨rfl,le_rfl⟩ hAcquire.resume.1

/-- A completed probability packet supplies this store to an actual PV read. -/
structure ProbabilityCellPublication (l : Launch) (X : Execution) (reader : EvId)
    (cell : Cell) where
  stage : Fin 2
  packet : Fin 2
  phase : Nat
  store : EvId
  credit : EvId
  wait : EvId
  acquire : MmaProbabilityAcquire l X reader stage packet wait
  release : ProbabilityCredit l X credit (reader.1/l.block) stage packet
  observed : MbarObserved X (.thread credit) (.thread wait)
  generation : probabilityOrdinal l X (reader.1/l.block) stage packet credit = phase
  pollBudget : okPolls (probabilityObject l (reader.1/l.block) stage packet)
    ((X.tr wait.1).take wait.2) ≤ phase
  cellWritten : StoreCell l X store cell
  footprint : TensorStoreFootprint l store cell (.probability stage)
  producer : store.1 = probabilityProducer l (reader.1/l.block) stage cell.lane
  completed : StoreDoneBefore l X store reader
  earlyVisit : packet = 0 → probabilityOrdinal l X (reader.1/l.block) stage 0 store = phase
  scoreBudget : phase + 1 ≤
    okPolls (scoreReadyObject l (reader.1/l.block) stage) ((X.tr store.1).take store.2)
  laterStoreBudget : ∀ other, StoreCell l X other cell →
    TensorStoreFootprint l other cell (.probability stage) → store.1 = other.1 →
    store.2 < other.2 → phase+2 ≤
      okPolls (scoreReadyObject l (reader.1/l.block) stage) ((X.tr other.1).take other.2)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Every actual Tensor Memory A read has a completed probability store into
its cell before the PV issue. Both physical packets are covered. -/
theorem probabilityCellPublication (hJoint : CorrectionJointGuards l X) {reader : EvId}
    {cell : Cell} (hRead : X.MmaACell reader cell) :
    Nonempty (ProbabilityCellPublication l X reader cell) := by
  obtain ⟨stage,⟨block,frag,d,op,acc,mask,index,byte,hBank,hPv,hCell⟩,hLo,hHi⟩ :=
    mmaAProbabilityTile hp hX hRead
  let cta := reader.1/l.block
  have hCta : cell.cta = cta := mmaAOperandCta hp hX hRead
  obtain ⟨_,_,hDesc,_⟩ := hPv.valueOperand hp hX
  have hRow : cell.lane < 128 := aCell_lane (by rw [hDesc]; decide) hCell
  have hReader := event_thread_lt hX hPv.decoded
  have hCtaBound : cta < l.grid := by
    change reader.1/l.block < l.grid
    change reader.1 < l.grid*l.block at hReader
    rw [hp.block] at hReader ⊢
    omega
  let g := probabilityProducer l cta stage cell.lane
  obtain ⟨hProducer,hOwner,hWarp,hLane⟩ := probabilityProducerGeometry hp cta stage hRow hCtaBound
  change g < l.threads at hProducer
  change g/l.block = cta at hOwner
  change warpIndex l g = 4*stage.val+cell.lane/32 at hWarp
  change laneBase l g+laneOf l g = cell.lane at hLane
  have hSameBank : warpIndex l g/4 = stage.val := by omega
  have hSoft : warpIndex l g < 8 := by have := stage.isLt; omega
  have hCells (n : Nat) (hn : n = cell.column) :
      (⟨cta,laneBase l g+laneOf l g,n⟩ : Cell) = cell := by
    rw [hLane,hn,← hCta]
  have hStoreFootprint {store : EvId} (hThread : store.1 = g) :
      TensorStoreFootprint l store cell (.probability stage) := by
    have hCtaStore : store.1/l.block = cta := by rw [hThread,hOwner]
    have hStage : warpIndex l store.1/4 = stage.val := hThread.symm ▸ hSameBank
    have hRowEq : cell.lane = Correction.rowOf l store.1 := by
      rw [hThread, ← hLane]
      unfold Correction.rowOf laneBase laneOf
      omega
    refine ⟨hCta.trans hCtaStore.symm,hRowEq,hLo,hHi,?_⟩
    change store.1%l.block/128 = stage.val
    unfold warpIndex at hStage
    omega
  by_cases hEarly : cell.column < probabilityColumn stage+48
  · obtain ⟨wait,hAcquire⟩ := hPv.probabilityAcquire hp hX 0 (.inl rfl)
    have hWait : MmaProbabilityAcquire l X reader stage 0 wait := hBank ▸ hAcquire
    obtain ⟨_,phase,poll,hRecord,hId,hOk,hPhase,hPollCount⟩ :=
      probabilityAcquireRecord hp hX hWait.event
    obtain ⟨credit,hCredit,hActor,hPhaseOrdinal,hObserve⟩ :=
      jointPollObservesLane hp hX hJoint stage hOwner hSoft hSameBank hRecord hOk hPhase
    have hCausal := probabilityCreditBeforeMma hp hX hCredit hWait (hId ▸ hObserve)
    let off := cell.column-probabilityColumn stage
    let quarter : Fin 3 := ⟨off/16,by dsimp [off]; omega⟩
    let word : Fin 16 := ⟨off%16,Nat.mod_lt _ (by decide)⟩
    have hCreditSoft : warpIndex l credit.1 < 8 := hActor.symm ▸ hSoft
    obtain ⟨store,hStore,hEarlier,hFoot,hVisit,_,hRival⟩ :=
      earlyProbabilityCellBeforeCreditAtVisit hp hX hCreditSoft hCredit quarter word
    have hDest : probabilityColumn stage+16*quarter.val+word.val = cell.column := by
      dsimp [quarter,word,off]
      omega
    rw [hActor,hCells _ hDest] at hFoot
    have hCtaStore : store.1/l.block = cta := by
      rw [hEarlier.1,hActor]
      exact hOwner
    have hCreditStore : ProbabilityCredit l X credit (store.1/l.block) stage 0 :=
      hCtaStore.symm ▸ hCredit
    have hProducer := hEarlier.1.trans hActor
    have hStage : warpIndex l store.1/4 = stage.val := hProducer.symm ▸ hSameBank
    have hBudget := hStore.scoreUses hp hX stage hStage
    change probabilityOrdinal l X (store.1/l.block) stage 0 store+1 ≤
      okPolls (scoreReadyObject l (store.1/l.block) stage) ((X.tr store.1).take store.2) at hBudget
    rw [hCtaStore,hVisit,hPhaseOrdinal] at hBudget
    refine ⟨⟨stage,0,phase,store,credit,wait,hWait,hCredit,hId ▸ hObserve,hPhaseOrdinal,
      hPollCount,hFoot,hStoreFootprint hProducer,hProducer,
      earlyProbabilityDoneThroughCredit hp hX stage hStore hCreditStore hEarlier hCausal,
      fun _ => hVisit.trans hPhaseOrdinal,hBudget,?_⟩⟩
    intro other hOther hOtherFoot hOtherActor hLater
    have hSameThread : other.1 = credit.1 := hOtherActor.symm.trans hEarlier.1
    have hOtherId : other = (credit.1,other.2) := Prod.ext hSameThread rfl
    have hOtherStage : warpIndex l other.1/4 = stage.val := hOtherActor ▸ hStage
    have hOtherCta := (hOtherFoot.cta.symm.trans hCta)
    have hCellOther := hOther
    rw [hOtherId,← hCells _ hDest,← hActor] at hCellOther
    have hAfter := hRival other.2 hLater hCellOther
    rw [hPhaseOrdinal,← hOtherId] at hAfter
    rcases probabilityStorePacketOfCell hp hX hOther hOtherFoot with ⟨early,_⟩ | ⟨_,hTail⟩
    · have hCount := early.scoreUses hp hX stage hOtherStage
      change probabilityOrdinal l X (other.1/l.block) stage 0 other+1 ≤
        okPolls (scoreReadyObject l (other.1/l.block) stage) ((X.tr other.1).take other.2) at hCount
      rw [hOtherCta] at hCount
      change phase+2 ≤ okPolls (scoreReadyObject l cta stage) ((X.tr other.1).take other.2)
      omega
    · omega
  · have hTail : probabilityColumn stage+48 ≤ cell.column := by omega
    have hAddr := hPv.probabilityAddress hp hX
    rw [hBank] at hAddr
    have hRange := (probabilityReadColumn ⟨_,hPv.decoded⟩ stage frag hAddr hRead).2
    have hFrag : 6 ≤ frag.val := by omega
    obtain ⟨wait,hAcquire⟩ := hPv.probabilityAcquire hp hX 1 (.inr hFrag)
    have hWait : MmaProbabilityAcquire l X reader stage 1 wait := hBank ▸ hAcquire
    obtain ⟨_,phase,poll,hRecord,hId,hOk,hPhase,hPollCount⟩ :=
      probabilityAcquireRecord hp hX hWait.event
    let warp : Fin 4 := ⟨cell.lane/32,by omega⟩
    obtain ⟨credit,hCredit,hCreditWarp,hPhaseOrdinal,hObserve⟩ :=
      tailCreditOfObservedWarpExact hp hX stage warp hRecord hOk hPhase
    have hCausal := probabilityCreditBeforeMma hp hX hCredit hWait (hId ▸ hObserve)
    have hCreditCta := (probabilityCreditRole hp hX stage 1 hCredit).1
    have hObserveCredit := hCredit
    obtain ⟨_,he⟩ := hObserveCredit
    have hSame : SameWarp l g credit.1 :=
      ⟨⟨hProducer,event_thread_lt hX he,hOwner.trans hCreditCta.symm⟩,
        hWarp.trans hCreditWarp.symm⟩
    let word : Fin 16 := ⟨cell.column-probabilityColumn stage-48,by omega⟩
    obtain ⟨store,hFoot,hDone,hProducer,hOrdinal,hRival⟩ :=
      tailProbabilityCellDoneThroughCreditAtVisit hp hX hSame hCredit hCausal word
    have hDest : probabilityColumn stage+48+word.val = cell.column := by
      dsimp [word]
      omega
    have hCtaStore : store.1/l.block = cta := by rw [hProducer,hOwner]
    have hStage : warpIndex l store.1/4 = stage.val := hProducer.symm ▸ hSameBank
    have hCellStore : StoreCell l X store cell := hCells _ hDest ▸ hFoot
    have hGeometry := hStoreFootprint hProducer
    obtain hEarlyStore | ⟨hTailStore,_⟩ := probabilityStorePacketOfCell hp hX hCellStore hGeometry
    · exact (Nat.not_lt_of_ge hTail hEarlyStore.2).elim
    have hBudget := tailProbabilityStoreScoreUses hp hX stage hTailStore hStage
    rw [hCtaStore] at hBudget
    rw [hPhaseOrdinal] at hOrdinal
    refine ⟨⟨stage,1,phase,store,credit,wait,hWait,hCredit,hId ▸ hObserve,hPhaseOrdinal,
      hPollCount,hCellStore,hGeometry,hProducer,hDone,
      fun h => ((by decide : (1 : Fin 2) ≠ 0) h).elim,
      (Nat.add_le_add_right hOrdinal 1).trans hBudget,?_⟩⟩
    intro other hOther hOtherFoot hOtherActor hLater
    have hSameThread : other.1 = g := hOtherActor.symm.trans hProducer
    have hOtherId : other = (g,other.2) := Prod.ext hSameThread rfl
    have hOtherStage : warpIndex l other.1/4 = stage.val := hOtherActor ▸ hStage
    have hOtherCta := hOtherFoot.cta.symm.trans hCta
    have hCellOther := hOther
    rw [hOtherId,← hCells _ hDest] at hCellOther
    have hAfter := hRival other.2 hLater hCellOther
    rw [hPhaseOrdinal,← hSameThread] at hAfter
    rcases probabilityStorePacketOfCell hp hX hOther hOtherFoot with ⟨_,hEarly⟩ | ⟨tail,_⟩
    · omega
    have hCount := tailProbabilityStoreScoreUses hp hX stage tail hOtherStage
    change warpBars X other.1 other.2+1 ≤
      okPolls (scoreReadyObject l (other.1/l.block) stage) ((X.tr other.1).take other.2) at hCount
    rw [hOtherCta] at hCount
    change phase < warpBars X other.1 other.2 at hAfter
    change phase+2 ≤ okPolls (scoreReadyObject l cta stage) ((X.tr other.1).take other.2)
    omega

/-- Every actual Tensor Memory A read has a completed probability store into its cell. -/
theorem probabilityStoreCandidateOfARead (hJoint : CorrectionJointGuards l X) {reader : EvId}
    {cell : Cell} (hRead : X.MmaACell reader cell) :
    ∃ store, StoreCell l X store cell ∧ StoreDoneBefore l X store reader := by
  obtain ⟨seen⟩ := probabilityCellPublication hp hX hJoint hRead
  exact ⟨seen.store,seen.cellWritten,seen.completed⟩

/-- The P store selected by the actual packet observes the reader's current score.
Both early and tail packets have the same exact score cursor at the consumer. -/
theorem ProbabilityCellPublication.exactScoreAndStoreCount (hCuQ : Epilogue.DrainCuQProtected p X)
    {reader : EvId} {cell : Cell} (seen : ProbabilityCellPublication l X reader cell)
    (hRead : X.MmaACell reader cell) :
    ∃ obs : ProbabilityStoreScore l X seen.store seen.stage,
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage obs.commit = seen.phase ∧
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage reader = seen.phase+1 ∧
      okPolls (scoreReadyObject l (reader.1/l.block) seen.stage)
        ((X.tr seen.store.1).take seen.store.2) = seen.phase+1 := by
  have hGuard : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨obs,hStoreExact⟩ := probabilityStoreObservesLatestScore hp hX hGuard seen.stage
    seen.cellWritten seen.footprint
  have hCta := (mmaAOperandCta hp hX hRead).symm.trans seen.footprint.cta
  obtain ⟨d,op,acc,mask,_,_,hMma,_⟩ := hRead
  have ⟨_,hMmaGet⟩ := hMma
  obtain ⟨_,_,_,_,⟨_,hStoreGet⟩,_,_⟩ := seen.cellWritten
  have hSame : SameCta l reader.1 seen.store.1 := ⟨event_thread_lt hX hMmaGet,
    event_thread_lt hX hStoreGet,hCta⟩
  have hPast : obs.commit.2 ≤ reader.2 := by
    by_contra! hAfter
    have hCycle := obs.doneBeforeEarlierMma hp hX hMma hSame hAfter
    exact tcStep_asymm hX (guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ))
      hCycle.tcStep seen.completed.tcStep
  have hObserved := scoreCommitCountBeforeMma hp hX hMma obs.score hCta hPast
  have hBudget := seen.scoreBudget
  have hMmaBudget := seen.acquire.coversScores
  have hPoll := seen.pollBudget
  rw [← hCta] at hStoreExact hObserved
  exact ⟨obs,by omega,by omega,by omega⟩

/-- The selected publication and the reading MMA use the same score visit. -/
theorem ProbabilityCellPublication.exactScore (hCuQ : Epilogue.DrainCuQProtected p X)
    {reader : EvId} {cell : Cell} (seen : ProbabilityCellPublication l X reader cell)
    (hRead : X.MmaACell reader cell) :
    ∃ obs : ProbabilityStoreScore l X seen.store seen.stage,
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage obs.commit = seen.phase ∧
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage reader = seen.phase+1 := by
  obtain ⟨obs,hOrdinal,hReader,_⟩ := seen.exactScoreAndStoreCount hp hX hCuQ hRead
  exact ⟨obs,hOrdinal,hReader⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
