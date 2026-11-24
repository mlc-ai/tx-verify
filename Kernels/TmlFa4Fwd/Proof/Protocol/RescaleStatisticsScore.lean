-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScorePollOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleStatistics
public import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
public import Lemmas.Protocol.UnitHandoff
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleScoreAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReadOrder
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.TcMma Thread Thread.Scores
open Prologue Epilogue
open Correction (rowOf statsBarrierId terminalStatsProducer terminalStatsCta terminalStatsWarp
  terminalStatsBarrier terminalStatsProducerWarp rescaleWaitOrdinalBoundsBeforeTerminal
  statsWaitHasWork)

/-- The statistics consumed by an actual rescale store trace back to their score notification. -/
structure RescaleStatisticsScore (l : Launch) (X : Execution) (store : EvId)
    (stage : Fin 2) where
  rendezvous : EvId
  acquire : EvId
  commit : EvId
  spec : TcCommit.Spec
  rank : Fin 16
  score : ScoreCommit l X commit (store.1/l.block) stage spec rank
  notified : rank ∈ X.tcNotified commit
  observed : WaitObserves X (.async commit (.tcNotify rank)) acquire
    (scoreReadyObject l (store.1/l.block) stage) true .cta
  afterAcquire : baseCausality l X acquire store
  acquireOwner : SameCta l acquire.1 store.1
  correctionWait : CorrectionWaits X rendezvous .rescale stage
  generation : scoreCommitOrdinal l X (store.1/l.block) stage commit =
    (correctionBefore X rendezvous).barrier (statsBarrierId l store.1 stage)
  creditCovered : probabilityOrdinal l X (store.1/l.block) stage 0 store ≤
    scoreCommitOrdinal l X (store.1/l.block) stage commit
  cursor : scoreCommitOrdinal l X (store.1/l.block) stage commit + 1 =
    (correctionBefore X store).barrier (statsBarrierId l store.1 stage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem rescaleStatisticsObservedScoreOfReturn (hCuQ : DrainCuQProtected p X)
    {store wait : EvId} {stage : Fin 2} (hWait : CorrectionWaits X wait .rescale stage)
    (hResume : Resumes kernel X wait store) (hPassed : wait.2+1 < store.2)
    (hCursor : (correctionBefore X store).barrier (statsBarrierId l store.1 stage) =
      (correctionBefore X wait).barrier (statsBarrierId l store.1 stage)+1)
    (hCredit : probabilityOrdinal l X (store.1/l.block) stage 0 store + 1 ≤
      (correctionBefore X store).barrier (statsBarrierId l store.1 stage)) :
    ∃ seen : RescaleStatisticsScore l X store stage,
      0 < scoreCommitOrdinal l X (store.1/l.block) stage seen.commit ∧
      scoreCommitOrdinal l X (store.1/l.block) stage seen.commit+1 =
        (correctionBefore X store).barrier (statsBarrierId l store.1 stage) := by
  obtain ⟨g,index⟩ := store
  obtain ⟨h,j⟩ := wait
  have hLane : h = g := hResume.1.1
  subst h
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  let n := (correctionBefore X (g,j)).barrier id
  have hId : 3 + warp.val = id := terminalStatsBarrier l g stage
  have hWarp : warpIndex l producer = warp.val := terminalStatsProducerWarp hp g stage
  have hSoft : warpIndex l producer < 8 := hWarp ▸ warp.isLt
  have hStage : warpIndex l producer / 4 = stage.val := by
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    rw [hWarp]
    change (rowOf l g / 32+4*stage.val)/4 = stage.val
    omega
  have hNamed : 3 + warpIndex l producer = id := (congrArg (3+·) hWarp).trans hId
  have hCta := terminalStatsCta hp g stage
  have hUsedK := usedKProtected hp hX
  have hWork : g/l.block < tilePrefix p p.batch * p.heads :=
    statsWaitHasWork hp hX hWait
  obtain ⟨batch,hb,hLo,hHi,hPositive,hTrip⟩ :=
    rescaleWaitOrdinalBoundsBeforeTerminal hp hX hWork hUsedK hWait
  change n < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 at hTrip
  have hPass : j + 1 < (X.tr g).length := hPassed.trans hResume.1.2.2
  obtain ⟨pos, round, hPub, hCount⟩ :=
    Statistics.publicationOfResumedRescale hp hX hCuQ hWait hPass
  change (before X (producer, pos)).notices = n at hCount
  have hFresh : round ≠ .final := by
    rintro rfl
    obtain ⟨selected,hS,hSLo,hSHi,hLower⟩ :=
      Softmax.finalPublicationOrdinalLower hp hX hSoft (hCta.symm ▸ hWork) hCuQ hUsedK hPub
    obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
    have hBatch : selected = batch :=
      (hUnique selected ⟨hS,hCta ▸ hSLo,hCta ▸ hSHi⟩).trans
        (hUnique batch ⟨hb,hLo,hHi⟩).symm
    rw [hBatch,hCta,hCount] at hLower
    exact hTrip.not_ge hLower
  have hBudget : n + (if round = .final then 1 else 0) < (before X (producer,pos)).notices+1 := by
    simp [hFresh,hCount]
  obtain ⟨hExists,hAcquire,hPublish⟩ :=
    statisticsScoreAcquireAtOrdinal hp hX stage hSoft hCta hStage hPub hBudget
  have hGuard : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨commit,spec,rank,hScore,hExact,hObserve⟩ :=
    scorePollObservesExactCommit hp hX hGuard stage hCta hSoft hStage hExists
  let poll := (producer,MbarRing.Poll.nth X (scoreReadyObject l (g/l.block) stage) producer n)
  have hSame : SameCta l poll.1 g := by
    obtain ⟨_,_,hGet,_⟩ := hAcquire
    obtain ⟨_, he, _⟩ := hWait
    exact ⟨event_thread_lt hX hGet,event_thread_lt hX he,hCta⟩
  have hPublicationOrd : (before X (producer,pos)).barrier (3+warpIndex l producer) =
      (correctionBefore X (g,j)).barrier (3+warpIndex l producer) := by
    exact (notificationOrdinal hp hX hSoft).symm.trans (hCount.trans
      (congrArg ((correctionBefore X (g, j)).barrier) hNamed).symm)
  have hCausal := Statistics.handoff hp hX hSame hNamed hPub hWait hPublicationOrd
    hPublish.1.2.1 hResume.1.2.1 hResume.1.2.2
  rw [hCursor] at hCredit
  change probabilityOrdinal l X (g/l.block) stage 0 (g,index)+1 ≤ n+1 at hCredit
  rw [← hExact] at hCredit
  exact ⟨⟨(g,j),poll,commit,spec,rank,hScore,hObserve.1,hAcquire.observes hObserve,
    hCausal,hSame,hWait,hExact,Nat.le_of_add_le_add_right hCredit,by rw [hExact,hCursor]⟩,
    by simpa only [hExact] using hPositive,
    by rw [hExact,hCursor]⟩

/-- The rescale store's selected score ordinal is the current correction
statistics count minus one. -/
theorem rescaleStatisticsObservedScoreWithOrdinal (hCuQ : DrainCuQProtected p X) {store : EvId}
    {stage : Fin 2} (hStore : OutputRescaleStore X store stage) :
    ∃ seen : RescaleStatisticsScore l X store stage,
      0 < scoreCommitOrdinal l X (store.1/l.block) stage seen.commit ∧
      scoreCommitOrdinal l X (store.1/l.block) stage seen.commit+1 =
        (correctionBefore X store).barrier (statsBarrierId l store.1 stage) := by
  obtain ⟨wait,hWait,hResume,hPassed,hCursor⟩ := statisticsPassedBeforeOutputRescale hp hX hStore
  exact rescaleStatisticsObservedScoreOfReturn hp hX hCuQ hWait hResume hPassed
    hCursor (hStore.creditUses hp hX)

/-- The returning rescale statistics rendezvous pairs with the same score generation
on its mapped softmax lane in every consistent prefix. -/
theorem rescaleStatisticsObservedScore (hCuQ : DrainCuQProtected p X) {store : EvId} {stage : Fin 2}
    (hStore : OutputRescaleStore X store stage) :
    Nonempty (RescaleStatisticsScore l X store stage) := by
  obtain ⟨seen,_⟩ := rescaleStatisticsObservedScoreWithOrdinal hp hX hCuQ hStore
  exact ⟨seen⟩

/-- The selected score ordinal of a recorded rescale load matches the
correction statistics count in its actual prefix. -/
theorem rescaleLoadStatisticsObservedScoreWithOrdinal (hCuQ : DrainCuQProtected p X) {load : EvId}
    {stage : Fin 2} (hLoad : OutputRescaleLoad X load stage) :
    ∃ seen : RescaleStatisticsScore l X load stage,
      0 < scoreCommitOrdinal l X (load.1/l.block) stage seen.commit ∧
      scoreCommitOrdinal l X (load.1/l.block) stage seen.commit+1 =
        (correctionBefore X load).barrier (statsBarrierId l load.1 stage) := by
  obtain ⟨wait,hWait,hResume,hPassed,hCursor⟩ := statisticsPassedBeforeOutputRescaleLoad hp hX hLoad
  exact rescaleStatisticsObservedScoreOfReturn hp hX hCuQ hWait hResume hPassed hCursor
    (hLoad.creditUses hp hX)

/-- An observed rescale load sees the same statistics and score protocol as the
corresponding rescale episode, even when its store has not happened yet. -/
theorem rescaleLoadStatisticsObservedScore (hCuQ : DrainCuQProtected p X) {load : EvId}
    {stage : Fin 2} (hLoad : OutputRescaleLoad X load stage) :
    ∃ seen : RescaleStatisticsScore l X load stage,
      0 < scoreCommitOrdinal l X (load.1/l.block) stage seen.commit := by
  obtain ⟨seen,hPositive,_⟩ := rescaleLoadStatisticsObservedScoreWithOrdinal hp hX hCuQ hLoad
  exact ⟨seen,hPositive⟩

/-- The rescale data access follows completion of every same-CTA MMA issued before
the score commit observed by its producer of statistics. -/
theorem RescaleStatisticsScore.doneBeforeEarlierMma {mma store : EvId} {stage : Fin 2}
    (h : RescaleStatisticsScore l X store stage) {d : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} (hMma : X.MmaIssue mma d op acc mask) (hSame : SameCta l mma.1 store.1)
    (hEarlier : mma.2 < h.commit.2) : DoneBefore l X mma store := by
  have hLane := mmaAndScoreCommitSameThread hp hX hMma h.score hSame.2.2
  have hTracks : TracksMma X mma h.commit :=
    ⟨hLane,hEarlier,.inl ⟨d,op,acc,mask,hMma⟩,h.spec,h.score.1⟩
  have hScope : SameCta l mma.1 h.acquire.1 :=
    ⟨hSame.1,h.acquireOwner.1,hSame.2.2.trans h.acquireOwner.2.2.symm⟩
  exact .inl ⟨h.acquire,.cta,
    ⟨_,_,⟨h.commit,h.spec,h.rank,rfl,hTracks,h.score.1,h.score.2,h.notified⟩,h.observed⟩,
    MbarRing.Unit.Gate.scopesMeet hScope .cluster .cta,h.afterAcquire⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
