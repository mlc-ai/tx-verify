-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsTripExtent
public import Kernels.TmlFa4Fwd.Proof.Thread.SharedWriterCoordinates
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemRescaleStatistics
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditGate
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.CorrectionCreditExtent
import Lemmas.Flow.NthEv
import Lemmas.Protocol.StagingHandoff

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Proof PTX.Flow Thread Prologue Epilogue
open Correction (terminalStatsProducer terminalStatsWarp terminalStatsCta terminalStatsBarrier
  terminalStatsProducerWarp statsBarrierId rescaleWaitOrdinalBeforeTerminal
  statsWaitHasWork terminalWaitOrdinalOfTrips)

private theorem publicationsBeforeEarlierStore {X : Execution} {g writer publication : Nat}
    {site : Fin 4} {round : Scores.Round} {a : Acc} {bytes : List Byte}
    (hStore : Scores.StatisticsStore X (g, writer) site a bytes)
    (hPub : Scores.Publishes X (g, publication) round)
    (hCount : (Scores.before X (g, writer)).notices ≤
      (Scores.before X (g, publication)).notices) :
    writer < publication := by
  obtain ⟨e, he, hNotice⟩ := hPub
  rcases Nat.lt_trichotomy writer publication with h | rfl | h
  · exact h
  · rw [hStore] at he
    have hKind := congrArg Event.kind (Option.some.inj he)
    simp [← hKind, Scores.notice] at hNotice
  · have hMark : Scores.publishesStats e = true := by simp [Scores.publishesStats, hNotice]
    have hNext := countP_take_succ he hMark
    have hLe := countP_take_mono Scores.publishesStats (X.tr g)
      (show publication + 1 ≤ writer from Nat.succ_le_of_lt h)
    rw [Scores.beforeNotices, Scores.beforeNotices] at hCount
    dsimp only at hCount
    omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem publicationOfResumedStatistics (hCuQ : DrainCuQProtected p X) {g wait batch : Nat}
    {stage : Fin 2} {waitRound : CorrectionRound}
    (hWait : CorrectionWaits X (g, wait) waitRound stage) (hPass : wait + 1 < (X.tr g).length)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hTrip : (correctionBefore X (g, wait)).barrier (statsBarrierId l g stage) ≤
      Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1) :
    ∃ pos round, Scores.Publishes X (terminalStatsProducer l g stage, pos) round ∧
      (Scores.before X (terminalStatsProducer l g stage, pos)).notices =
        (correctionBefore X (g, wait)).barrier (statsBarrierId l g stage) := by
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  let n := (correctionBefore X (g, wait)).barrier id
  have hId : 3 + warp.val = id := terminalStatsBarrier l g stage
  have hWarp : warpIndex l producer = warp.val := terminalStatsProducerWarp hp g stage
  have hSoft : warpIndex l producer < 8 := hWarp.symm ▸ warp.isLt
  have hMember : warpIndex l producer ∈ statsParticipants warp := by
    rw [hWarp]
    exact Finset.mem_insert_self ..
  have hNamed : 3 + warpIndex l producer = id := (congrArg (3 + ·) hWarp).trans hId
  have hCta := terminalStatsCta hp g stage
  have hUsedK := usedKProtected hp hX
  have hWork := statsWaitHasWork hp hX hWait
  have hOrd : observedBarrierOrdinal X (g, wait) id = n :=
    (correctionBarrierOrdinal X (g, wait) id).symm
  obtain ⟨_, ⟨e, he, hKind, _, _⟩, _⟩ := correctionWaits hp hX hWait
  have hArrival : BarrierArrival X (g, wait) id (some 64) .sync := ⟨e, he, hKind⟩
  obtain ⟨pos, mode, hPeer, hGen⟩ := memberBarrierArrival hX
    (hId ▸ statsBarrierSources hp hX warp) (hId ▸ statsBarrierShape hp warp)
    hArrival hPass hCta hMember (by
      rintro ⟨exit, stop, hGet, hExit⟩
      have hExtent := ordinalBeforeActiveExit hp hX hCuQ hUsedK
        (ordinal := n) hSoft (hCta.symm ▸ hWork) hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
        (by rw [hCta]; exact hTrip) hGet hExit
      have hMono : (Scores.before X (producer, exit)).notices ≤
          (Scores.before X (producer, (X.tr producer).length)).notices := by
        rw [Scores.beforeNotices, Scores.beforeNotices]
        exact countP_take_mono _ _ (len_of_get hGet).le
      obtain ⟨pos, hRelease, hOrd'⟩ :=
        Scores.publicationAtOrdinal hp hX hSoft (hExtent.trans_le hMono)
      rw [hNamed] at hRelease hOrd'
      exact ⟨pos, .arrive, hRelease, hOrd'.trans hOrd.symm⟩)
  have hWitness : BarrierArrival X (producer, pos) (3 + warpIndex l producer) (some 64) mode :=
    hNamed.symm ▸ hPeer
  obtain ⟨round, hPub⟩ := Scores.publishesAtStatisticsBarrier hp hX hSoft hWitness
  refine ⟨pos, round, hPub, ?_⟩
  rw [Scores.notificationOrdinal hp hX hSoft, Scores.barrierOrdinal, hNamed]
  exact hGen.trans hOrd

/-- A returned rescale wait observes the paired softmax producer's publication of that
statistics generation. -/
theorem publicationOfResumedRescale (hCuQ : DrainCuQProtected p X) {g wait : Nat} {stage : Fin 2}
    (hWait : CorrectionWaits X (g, wait) .rescale stage) (hPass : wait + 1 < (X.tr g).length) :
    ∃ pos round, Scores.Publishes X (terminalStatsProducer l g stage, pos) round ∧
      (Scores.before X (terminalStatsProducer l g stage, pos)).notices =
        (correctionBefore X (g, wait)).barrier (statsBarrierId l g stage) := by
  have hWork := statsWaitHasWork hp hX hWait
  have hUsedK := usedKProtected hp hX
  obtain ⟨batch, hb, hLo, hHi, hTrip⟩ :=
    rescaleWaitOrdinalBeforeTerminal hp hX hWork hUsedK hWait
  exact publicationOfResumedStatistics hp hX hCuQ hWait hPass hb hLo hHi hTrip.le

/-- A returned terminal wait observes the paired softmax producer's publication of that
statistics generation. -/
theorem publicationOfResumedTerminal (hCuQ : DrainCuQProtected p X) {g wait : Nat} {stage : Fin 2}
    (hWait : CorrectionWaits X (g, wait) .terminal stage) (hPass : wait + 1 < (X.tr g).length) :
    ∃ pos round, Scores.Publishes X (terminalStatsProducer l g stage, pos) round ∧
      (Scores.before X (terminalStatsProducer l g stage, pos)).notices =
        (correctionBefore X (g, wait)).barrier (statsBarrierId l g stage) := by
  have hWork := statsWaitHasWork hp hX hWait
  have hUsedK := usedKProtected hp hX
  obtain ⟨batch, hb, hLo, hHi, hTrip⟩ :=
    terminalWaitOrdinalOfTrips hp hX hWork hUsedK hWait
  exact publicationOfResumedStatistics hp hX hCuQ hWait hPass hb hLo hHi hTrip.le

/-- A statistics writer in an earlier or the matching generation precedes the correction
role's statistics read. -/
theorem statisticsStoreBeforeRead (hCuQ : DrainCuQProtected p X) {writer reader : EvId}
    {stage : Fin 2} {site : Fin 4} {kind : Correction.StatsKind} {a b : Acc} {data : List Byte}
    {bytes : List (Option Byte)} (hStore : Scores.StatisticsStore X writer site a data)
    (hRead : Thread.Correction.StatisticsRead X reader stage kind b bytes)
    (hPair : writer.1 = terminalStatsProducer l reader.1 stage)
    (hWithin : (Scores.before X writer).notices <
      (correctionBefore X reader).barrier (statsBarrierId l reader.1 stage)) :
    baseCausality l X writer reader := by
  obtain ⟨h, index⟩ := reader
  obtain ⟨g, j⟩ := writer
  dsimp only at hPair
  subst g
  obtain ⟨⟨consumer, wait⟩, hWait, hResume, hOrdinal⟩ :=
    statisticsBeforeRead hp hX hRead
  have hLane : consumer = h := hResume.1.1
  subst consumer
  have hPass : wait + 1 < (X.tr h).length :=
    (Nat.succ_le_of_lt hResume.1.2.1).trans_lt hResume.1.2.2
  obtain ⟨pos, round, hPub, hOrd⟩ : ∃ pos round,
      Scores.Publishes X (terminalStatsProducer l h stage, pos) round ∧
      (Scores.before X (terminalStatsProducer l h stage, pos)).notices =
        (correctionBefore X (h, wait)).barrier (statsBarrierId l h stage) := by
    cases kind
    · exact publicationOfResumedRescale hp hX hCuQ hWait hPass
    · exact publicationOfResumedTerminal hp hX hCuQ hWait hPass
    · exact publicationOfResumedTerminal hp hX hCuQ hWait hPass
  let producer := terminalStatsProducer l h stage
  have hCta : producer / l.block = h / l.block := terminalStatsCta hp h stage
  have hSame : SameCta l producer h := ⟨event_thread_lt hX hStore, event_thread_lt hX hRead, hCta⟩
  have hNamed : Paired l producer h stage := by
    unfold Paired producer
    rw [terminalStatsProducerWarp hp]
    exact terminalStatsBarrier l h stage
  have hSoft : warpIndex l producer < 8 :=
    (terminalStatsProducerWarp hp h stage).symm ▸ (terminalStatsWarp l h stage).isLt
  have hNotices : (Scores.before X (producer, j)).notices ≤
      (Scores.before X (producer, pos)).notices := by
    change (Scores.before X (producer, j)).notices <
      (correctionBefore X (h, index)).barrier (statsBarrierId l h stage) at hWithin
    rw [hOrd]
    change (correctionBefore X (h, index)).barrier (statsBarrierId l h stage) =
      (correctionBefore X (h, wait)).barrier (statsBarrierId l h stage) + 1 at hOrdinal
    omega
  have hBefore := publicationsBeforeEarlierStore hStore hPub hNotices
  have hMatch := (Scores.notificationOrdinal hp hX (j := pos) hSoft).symm.trans hOrd
  refine handoff hp hX hSame hNamed hPub hWait ?_ hBefore hResume.1.2.1 hResume.1.2.2
  exact hMatch.trans (congrArg ((correctionBefore X (h, wait)).barrier) hNamed).symm

/-- A later writer acquires its buffer through the reader's credit of that read's generation. -/
theorem statisticsReadBeforeStore (hCuQ : DrainCuQProtected p X) {writer reader : EvId}
    {stage : Fin 2} {site : Fin 4} {kind : Correction.StatsKind} {a b : Acc} {data : List Byte}
    {bytes : List (Option Byte)} (hStore : Scores.StatisticsStore X writer site a data)
    (hRead : Thread.Correction.StatisticsRead X reader stage kind b bytes)
    (hPair : writer.1 = terminalStatsProducer l reader.1 stage)
    (hLater : (correctionBefore X reader).barrier (statsBarrierId l reader.1 stage) ≤
      (Scores.before X writer).notices) :
    baseCausality l X reader writer := by
  rcases reader with ⟨g, j⟩
  rcases writer with ⟨producer, index⟩
  let q := (correctionBefore X (g, j)).count (.statsCredit stage)
  have hWarp := hRead.warp hp hX
  have hLen := len_of_get (show X.get (g, j) = some _ from hRead)
  have hWaitCount : (correctionBefore X (g,j)).barrier (statsBarrierId l g stage) = q + 1 := by
    rw [correctionBarrierOrdinal, ← Correction.correctionWaitPrefixCount hp hX stage hLen hWarp,
      Correction.statisticsReadBeforeCredit hX stage kind hRead,
      ← Correction.correctionCreditCursor hp hX stage hRead]
  change (correctionBefore X (g,j)).barrier (statsBarrierId l g stage) ≤ _ at hLater
  rw [hWaitCount] at hLater
  obtain ⟨poll, _, hAcquire, hOrdinal, hResume⟩ :=
    Scores.acquireBeforeStatisticsStore hp hX hStore hLater
  have hOwner : producer / l.block = g / l.block :=
    (congrArg (· / l.block) hPair).trans (terminalStatsCta hp g stage)
  have hStage : stage.val = warpIndex l producer / 4 := by
    change producer = terminalStatsProducer l g stage at hPair
    rw [hPair, terminalStatsProducerWarp hp]
    have hRow : Correction.rowOf l g < 128 := Nat.mod_lt _ (by decide)
    change stage.val = (Correction.rowOf l g / 32 + 4 * stage.val) / 4
    omega
  obtain ⟨lane, hLane⟩ := Correction.statsCreditLaneOf hOwner.symm hWarp.1 hWarp.2
  obtain ⟨credit, hUse, hSync⟩ := creditHandoff hp hX hCuQ (producer, poll)
    stage hAcquire hStage q hOrdinal lane
  change g = Correction.statsCreditLane l (producer / l.block) lane at hLane
  rw [← hLane] at hUse hSync
  have hBefore : j ≤ credit := by
    obtain ⟨e, he, ha⟩ := hSync.arrives
    have hArrival := Correction.statsCreditArrivalCursor hp hX stage he
    have hReadCursor := Correction.statsCreditArrivalCursor hp hX stage hRead
    rw [← hOwner] at hArrival hReadCursor
    exact MbarRing.arrival_index_ge he ha (hArrival.trans hUse) hReadCursor.le
  obtain ⟨release, hRelease, acquire, hObserve, hScope⟩ := hSync
  exact Staging.baseCausality_of_handoff hRelease hObserve hScope
    ⟨rfl, hBefore⟩ hResume.1

/-- Correction statistics reads and the softmax stores of their bytes always have a byte order. -/
theorem statisticsAccessOrder (hCuQ : DrainCuQProtected p X) {writer reader : EvId} {stage : Fin 2}
    {kind : Correction.StatsKind} {a b : Acc} {data : List Byte} {bytes : List (Option Byte)}
    {loc : Loc} (hWrite : X.Writes writer a data)
    (hRead : Thread.Correction.StatisticsRead X reader stage kind b bytes) (ha : a.Covers loc)
    (hb : b.Covers loc) :
    ByteCausality l X loc (.thread writer) (.thread reader) ∨
      ByteCausality l X loc (.thread reader) (.thread writer) := by
  obtain ⟨hPair, site, hStore, _⟩ := ordinaryStatisticsWriter hp hX hWrite hRead ha hb
  by_cases hLater : (correctionBefore X reader).barrier (statsBarrierId l reader.1 stage) ≤
      (Scores.before X writer).notices
  · exact .inr (.direct (.inl (statisticsReadBeforeStore hp hX hCuQ hStore hRead hPair hLater)))
  · exact .inl (.direct (.inl
      (statisticsStoreBeforeRead hp hX hCuQ hStore hRead hPair (by omega))))

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
