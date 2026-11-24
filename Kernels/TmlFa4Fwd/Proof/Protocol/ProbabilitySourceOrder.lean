-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityOperandSources
import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
import Kernels.TmlFa4Fwd.Proof.Thread.TmemScoreToProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Protocol.StagingHandoff
import Lemmas.Protocol.UnitGate
import Lemmas.Tcgen05.TcFence
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier PTX.TcMma Thread Thread.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

private theorem earlyWaitOrdinalBeforeMma {reader wait : EvId} {d : Nat} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} (hReader : X.MmaIssue reader d op acc mask) (stage : Fin 2)
    (hWait : ScoreAcquire X wait (probabilityObject l (reader.1/l.block) stage 0))
    (hResumes : Resumes kernel X wait reader) :
    okPolls (probabilityObject l (reader.1/l.block) stage 0) ((X.tr wait.1).take wait.2)+1 ≤
      scoreCommitOrdinal l X (reader.1/l.block) stage reader := by
  let cta := reader.1/l.block
  let target := probabilityObject l cta stage 0
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨_,phase,poll,hPoll,hId,hSuccess,hPhase,hOrdinal⟩ :=
    probabilityAcquireRecord hp hX hWait
  obtain ⟨credit,hCredit,hSoft,hCreditOrdinal,hObserved⟩ :=
    jointPollObservesSoftmax hp hX hJoint stage hPoll hSuccess hPhase
  rw [hId] at hObserved
  obtain ⟨position,_,scorePhase,score,hScore,hScoreId,hScoreSuccess,hBeforeCredit,hScorePhase,
      hCreditBound⟩ := scoreObservedBeforeSoftmaxCredit hp hX stage 0 hSoft hCredit
  obtain ⟨commit,spec,rank,hCommit,hCommitOrdinal,hScoreObserved⟩ :=
    scoreCommitOfObservation hp hX stage hScore hScoreSuccess hScorePhase
  rw [hScoreId] at hScoreObserved
  have hScoreWait := scoreAcquireOfRecord hp hX (wait := (credit.1,position)) stage
    hSoft hScore hScoreId hScoreSuccess
  have hOwner := (probabilityCreditRole hp hX stage 0 hCredit).1
  have ⟨_,_,he,_⟩ := hWait
  have ⟨_,_,hf,_⟩ := hScoreWait
  have ⟨_,hr⟩ := hReader
  have hSame : SameCta l credit.1 wait.1 :=
    ⟨event_thread_lt hX (e := (credit.1,position)) hf,event_thread_lt hX he,
    hOwner.trans (congrArg (·/l.block) hResumes.1.1).symm⟩
  have hBefore : baseCausality l X (credit.1,position) reader :=
    Staging.baseCausality_of_handoff (⟨0,1,hCredit⟩ : MbarRelease X credit target .cta)
      (hWait.observes hObserved) (MbarRing.Unit.Gate.scopesMeet hSame .cta .cta)
      ⟨rfl,hBeforeCredit.1.2.1.le⟩ hResumes.1
  have hLater : commit.2 ≤ reader.2 := by
    by_contra! hEarlier
    have hLane := mmaAndScoreCommitSameThread hp hX hReader hCommit rfl
    have hTracks : TracksMma X reader commit :=
      ⟨hLane,hEarlier,.inl ⟨d,op,acc,mask,hReader⟩,spec,hCommit.1⟩
    have hScope : SameCta l reader.1 credit.1 := ⟨event_thread_lt hX hr,
      event_thread_lt hX (e := (credit.1,position)) hf,hOwner.symm⟩
    have hCycle : DoneBefore l X reader reader := .inl ⟨(credit.1,position),.cta,
      ⟨_,_,⟨commit,spec,rank,rfl,hTracks,hCommit.1,hCommit.2,hScoreObserved.1⟩,
        hScoreWait.observes hScoreObserved⟩,
      MbarRing.Unit.Gate.scopesMeet hScope .cluster .cta,hBefore⟩
    exact tcStep_acyclic hX (guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ))
      reader hCycle.tcStep
  have hCount := scoreCommitCountBeforeMma hp hX hReader hCommit rfl hLater
  omega

/-- Every earlier overlapping QK has completed before the P store selected by
the current probability packet, including a store of the tail packet. -/
theorem ProbabilityCellPublication.earlierQkBeforeStore {reader writer : EvId} {cell : Cell}
    (seen : ProbabilityCellPublication l X reader cell) (hRead : X.MmaACell reader cell)
    (hWriter : X.MmaCell writer cell) (hEarlier : writer.2 < reader.2)
    : DoneBefore l X writer seen.store := by
  obtain ⟨obs,hExact,hCount⟩ := seen.exactScore hp hX hCuQ hRead
  obtain ⟨stage,hPv,hLo,hHi⟩ := mmaAProbabilityTile hp hX hRead
  have hStage : stage = seen.stage := by
    have hLow := seen.footprint.columnLo
    have hHigh := seen.footprint.columnHi
    generalize hBank : seen.stage = other at hLow hHigh ⊢
    fin_cases stage <;> fin_cases other <;> first | rfl |
      (simp [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hLow hHigh hLo hHi; omega)
  subst stage
  obtain ⟨wd,wo,wa,wm,wr,wc,hWrite,hWritten⟩ := hWriter
  have hQk := mmaAccumulatorOnTile hp hX (tile := .probability seen.stage)
    ⟨hLo,hHi⟩ hWrite (writeCell_resultCell hWritten)
  have hCellWriter : X.MmaCell writer cell := ⟨wd,wo,wa,wm,wr,wc,hWrite,hWritten⟩
  obtain ⟨wait,hGuard⟩ := scoreToPvGuard hp hX seen.stage hCellWriter hQk hPv hEarlier
  have hCta := (mmaAOperandCta hp hX hRead).symm.trans seen.footprint.cta
  obtain ⟨d,op,acc,mask,_,_,hReader,_⟩ := hRead
  have hBound := earlyWaitOrdinalBeforeMma hp hX hCuQ hReader seen.stage
    hGuard.acquire hGuard.returns
  have hCover : okPolls (probabilityObject l (reader.1/l.block) seen.stage 0)
      ((X.tr wait.1).take wait.2) ≤
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage obs.commit := by omega
  have hBefore := hGuard.beforeCommit (hCta.symm ▸ obs.score) hCover
  have hIssuer := (mmaWrittenCellCta hp hX hCellWriter).symm.trans seen.footprint.cta
  have ⟨_,he⟩ := hWrite
  have ⟨_,_,_,_,⟨_,hf⟩,_,_⟩ := seen.cellWritten
  exact obs.doneBeforeEarlierMma hp hX hWrite
    ⟨event_thread_lt hX he,event_thread_lt hX hf,hIssuer⟩ hBefore

omit hp hX hCuQ in
private theorem probabilityFootprintAtCell {l : Launch} {a b : EvId} {cell : Cell}
    {stage : Fin 2} {tile : TensorStoreTile}
    (ha : TensorStoreFootprint l a cell (.probability stage))
    (hb : TensorStoreFootprint l b cell tile) : tile = .probability stage := by
  have hLo := ha.columnLo
  have hHi := ha.columnHi
  have hOtherLo := hb.columnLo
  have hOtherHi := hb.columnHi
  cases tile with
  | probability written =>
    suffices written = stage by rw [this]
    apply Fin.ext
    simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hLo hHi hOtherLo hOtherHi
    omega
  | rescale written =>
    have hEnd := probabilityColumn_range stage
    have hScore := scoreColumn_range stage
    simp only [TensorStoreTile.columns,outputColumn] at hOtherLo
    change cell.column < probabilityColumn stage+64 at hHi
    omega

/-- Each other store of this cell precedes the selected store or follows the PV reader. -/
theorem ProbabilityCellPublication.competingStoreOrder {reader other : EvId} {cell : Cell}
    (seen : ProbabilityCellPublication l X reader cell) (hRead : X.MmaACell reader cell)
    (hOther : StoreCell l X other cell) :
    other = seen.store ∨ WriteBefore l X other seen.store ∨ DoneBefore l X reader other := by
  obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hOther
  obtain rfl := probabilityFootprintAtCell seen.footprint hFoot
  have hCta : reader.1/l.block = other.1/l.block :=
    (mmaAOperandCta hp hX hRead).symm.trans hFoot.cta
  have hCtaStore : reader.1/l.block = seen.store.1/l.block :=
    (mmaAOperandCta hp hX hRead).symm.trans seen.footprint.cta
  obtain ⟨_,_,hReaderCount⟩ := seen.exactScore hp hX hCuQ hRead
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨obs,hOtherCount⟩ := probabilityStoreObservesLatestScore hp hX hJoint
    seen.stage hOther hFoot
  obtain ⟨d,op,acc,mask,_,_,hMma,_⟩ := hRead
  have ⟨_,he⟩ := hMma
  have ⟨_,_,_,_,⟨_,hf⟩,_,_⟩ := hOther
  have hSame : SameCta l reader.1 other.1 :=
    ⟨event_thread_lt hX he,event_thread_lt hX hf,hCta⟩
  by_cases hLater : reader.2 < obs.commit.2
  · exact .inr (.inr (obs.doneBeforeEarlierMma hp hX hMma hSame hLater))
  have hBound := scoreCommitCountBeforeMma hp hX hMma obs.score hCta (by omega)
  rw [← hCta] at hBound hOtherCount
  have hActor := sameTensorStoreLane hp hX hOther seen.cellWritten
  let object := scoreReadyObject l (reader.1/l.block) seen.stage
  have hOtherBound : okPolls object ((X.tr other.1).take other.2) ≤ seen.phase+1 := by
    dsimp only [object]
    omega
  have hAtMost : other.2 ≤ seen.store.2 := by
    by_contra! hAfter
    have hBudget := seen.laterStoreBudget other hOther hFoot hActor.symm hAfter
    change seen.phase+2 ≤ okPolls object ((X.tr other.1).take other.2) at hBudget
    omega
  rcases Nat.lt_or_eq_of_le hAtMost with hBefore | hEq
  · refine .inr (.inl ?_)
    rcases tensorStoreWritesOrdered hp hX hOther seen.cellWritten with h | h | h
    · exact ((Nat.ne_of_lt hBefore) (congrArg Prod.snd h)).elim
    · exact h
    · have hSync := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
      have hReverse := tcStep_same_thread (tcStep_acyclic hX hSync) h.tcStep hActor.symm
        (by rw [hf]; rfl)
      omega
  · exact .inl (Prod.ext hActor hEq)

/-- The probability cell selected by the acquire is the stable source of the PV A read. -/
theorem ProbabilityCellPublication.readSource {reader : EvId} {cell : Cell}
    (seen : ProbabilityCellPublication l X reader cell) (hRead : X.MmaACell reader cell)
    : ReadSource l X .a seen.store reader cell := by
  have ⟨d,op,acc,mask,_,_,hMma,_⟩ := hRead
  have hSync := guardedOfTmaSafe hX (Safety.noTmaUnsafe hp hX hCuQ)
  have hReads := (readsSafe_iff.mp (Safety.tensorReadsSafeOfCuQ hp hX hCuQ)).2.1
  have hLife := (Safety.mmaAccessLifetime hp hX hCuQ (.inr (.inr hRead))).2
  refine ⟨(mmaIssueNeStore hMma seen.cellWritten).symm,.inr (.inl seen.cellWritten),
    .inr (.inl seen.completed),?_,?_⟩
  · intro other hRival
    rcases hRival with hOtherMma | hOtherStore | hOtherCopy | hOtherShift
    · by_cases hBefore : other.2 < reader.2
      · exact .inr (.inl (.inl (.inl (seen.earlierQkBeforeStore hp hX hCuQ
          hRead hOtherMma hBefore))))
      rcases hReads reader other cell hRead (.inl hOtherMma) with hSame | hWrong | hReadBefore
      · exact .inr (.inr (.inl hSame.symm))
      · have hLane := (mmaAAndDLane hp hX hRead hOtherMma).symm
        exact (hBefore (tcStep_same_thread (tcStep_acyclic hX hSync) hWrong.tcStep
          hLane (mmaIsNotOrdinaryAccess hMma))).elim
      · exact .inr (.inr hReadBefore)
    · rcases seen.competingStoreOrder hp hX hCuQ hRead hOtherStore with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inr (.inl h)))
    · obtain ⟨_,_,_,_,hCopy,_⟩ := hOtherCopy
      exact (noTensorCopyOperandIssue hX hCopy).elim
    · obtain ⟨_,hShift,_⟩ := hOtherShift
      exact (noTensorShiftIssue hX hShift).elim
  · intro cta record hRecord hCover release hRelease
    exact .inl (hLife cta record hRecord hCover release hRelease)


end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
