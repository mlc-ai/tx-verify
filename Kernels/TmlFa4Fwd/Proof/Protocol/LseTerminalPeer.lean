-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseStatistics
public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsTripExtent
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Lemmas.Order.DependencyWitness
import Lemmas.Protocol.NamedBarArrive

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow Thread Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

private theorem terminalWaitArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait : Nat} {stage : Fin 2} (hWait : CorrectionWaits X (g,wait) .terminal stage) :
    BarrierArrival X (g,wait) (statsBarrierId l g stage) (some 64) .sync := by
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := correctionWaits hp hX hWait
  exact ⟨e,he,hKind⟩

private theorem waitArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {stage : Fin 2} {wait : Nat} {sum max : List (Option Byte)}
    (hReads : Thread.Correction.TerminalLseReads l X store stage wait sum max) :
    BarrierArrival X (store.1, wait) (statsBarrierId l store.1 stage) (some 64) .sync ∧
      wait + 1 < (X.tr store.1).length := by
  obtain ⟨_,hLast⟩ := hReads.maxRead
  have hLen : wait+2 < (X.tr store.1).length := PTX.len_of_get hLast
  exact ⟨terminalWaitArrival hp hX hReads.terminal,by omega⟩

/-- The actual softmax lane selected by the row and stage participates in the released wait. -/
structure TerminalPeer (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (wait pos : Nat) (round : Scores.Round) : Prop where
  publication : Scores.Publishes X (terminalStatsProducer l g stage, pos) round
  ordinal : observedBarrierOrdinal X (terminalStatsProducer l g stage, pos)
      (statsBarrierId l g stage) = observedBarrierOrdinal X (g, wait) (statsBarrierId l g stage)
  sameGeneration : ∃ key, CtaBarArrivalK l X (terminalStatsProducer l g stage, pos) key ∧
    CtaBarK l X (g, wait) key ∧ CtaBarDone l X (g / l.block) key
  witnessed : Witness l X (.thread (terminalStatsProducer l g stage, pos)) (g, wait)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem terminalPeerOfArrival {g wait pos : Nat} {stage : Fin 2} {mode : BarMode}
    (hWait : BarrierArrival X (g, wait) (statsBarrierId l g stage) (some 64) .sync)
    (hPass : wait + 1 < (X.tr g).length)
    (hArrival : BarrierArrival X (terminalStatsProducer l g stage, pos)
      (statsBarrierId l g stage) (some 64) mode)
    (hOrd : observedBarrierOrdinal X (terminalStatsProducer l g stage, pos)
      (statsBarrierId l g stage) = observedBarrierOrdinal X (g, wait) (statsBarrierId l g stage)) :
    ∃ round, TerminalPeer l X g stage wait pos round := by
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  have hId : 3 + warp.val = id := terminalStatsBarrier l g stage
  have hCta : producer / l.block = g / l.block := terminalStatsCta hp g stage
  have hWarp := terminalStatsProducerWarp hp g stage
  have hw : warpIndex l producer < 8 := hWarp ▸ warp.isLt
  have hId' : 3 + warpIndex l producer = id := (congrArg (3 + ·) hWarp).trans hId
  have hSources := hId ▸ statsBarrierSources hp hX warp
  have hShape := hId ▸ statsBarrierShape hp warp
  have hObserved : BarrierArrival X (producer, pos) (3 + warpIndex l producer) (some 64) mode := by
    rw [hId']
    exact hArrival
  obtain ⟨round, hPub⟩ := Scores.publishesAtStatisticsBarrier hp hX hw hObserved
  obtain ⟨key, hKey, hDone⟩ := barrierSyncReturned hX hWait hPass
  have hKeyExact := hSources.arrival_kind_key hX hShape hWait hKey.arrival
  change key = id + 16 * observedBarrierOrdinal X (g, wait) id at hKeyExact
  have hRem : key % 16 = id := by have := hShape.id_lt; omega
  have hQuot : key / 16 = observedBarrierOrdinal X (g, wait) id := by
    have := hShape.id_lt
    omega
  have hReleased : CtaBarrier.Released l.block (X.barriers (producer / l.block)) id
      (observedBarrierOrdinal X (producer, pos) id) := by
    rw [hCta, hOrd, ← hRem, ← hQuot]
    exact hDone
  have hArrivalKey := barrierArrivalKeyOfReleased hX hSources hShape hArrival hReleased
  rw [hOrd, ← hKeyExact] at hArrivalKey
  obtain ⟨finish, hComplete⟩ := hDone
  exact ⟨round, hPub, hOrd, ⟨key, hArrivalKey, hKey, finish, hComplete⟩,
    Witness.of_ctaBarCounted hKey hComplete hArrivalKey hCta⟩

/-- When the producer has enough publications before any exit, the already released wait
selects its actual publication of the same generation. -/
private theorem terminalPeerAtWaitOfExitedExtent {g wait : Nat} {stage : Fin 2}
    (terminal : CorrectionWaits X (g,wait) .terminal stage) (hPass : wait+1 < (X.tr g).length)
    (hExtent : let producer := terminalStatsProducer l g stage
      Exited X producer → observedBarrierOrdinal X (g, wait)
          (statsBarrierId l g stage) <
        (Scores.before X (producer, (X.tr producer).length)).notices) :
    ∃ pos round, TerminalPeer l X g stage wait pos round := by
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  have hId := terminalStatsBarrier l g stage
  have hWarp := terminalStatsProducerWarp hp g stage
  have hw : warpIndex l producer < 8 := hWarp ▸ warp.isLt
  have hId' : 3 + warpIndex l producer = statsBarrierId l g stage :=
    (congrArg (3 + ·) hWarp).trans hId
  have hMember : warpIndex l producer ∈ statsParticipants warp := by
    rw [hWarp]
    exact Finset.mem_insert_self ..
  have hWait := terminalWaitArrival hp hX terminal
  obtain ⟨pos, mode, hArrival, hOrd⟩ := memberBarrierArrival hX
    (hId ▸ statsBarrierSources hp hX warp) (hId ▸ statsBarrierShape hp warp)
    hWait hPass (terminalStatsCta hp g stage) hMember (fun hExit => by
      obtain ⟨pos, hA, hOrd⟩ := Scores.publicationAtOrdinal hp hX hw (hExtent hExit)
      exact ⟨pos, .arrive, hId' ▸ hA, hId' ▸ hOrd⟩)
  obtain ⟨round, hPeer⟩ := terminalPeerOfArrival hp hX hWait hPass hArrival hOrd
  exact ⟨pos, round, hPeer⟩

/-- One lane has at most one observed publication in a generation. -/
theorem TerminalPeer.unique {g wait i j : Nat} {stage : Fin 2}
    {firstRound secondRound : Scores.Round} (hi : TerminalPeer l X g stage wait i firstRound)
    (hj : TerminalPeer l X g stage wait j secondRound) :
    i = j ∧ firstRound = secondRound := by
  let producer := terminalStatsProducer l g stage
  have hId : 3 + warpIndex l producer = statsBarrierId l g stage :=
    (congrArg (3 + ·) (terminalStatsProducerWarp hp g stage)).trans (terminalStatsBarrier l g stage)
  have hOrder {a b : Nat} {r s : Scores.Round} (ha : TerminalPeer l X g stage wait a r)
      (hb : TerminalPeer l X g stage wait b s) (hlt : a < b) : False := by
    have h := Scores.publicationOrdinalIncreases hp hX ha.publication hlt
    rw [Scores.observedOrdinal, Scores.observedOrdinal, hId, ha.ordinal, hb.ordinal] at h
    exact (Nat.lt_irrefl _) h
  have hPos : i = j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact (hOrder hi hj h).elim
    · exact h
    · exact (hOrder hj hi h).elim
  subst j
  obtain ⟨e, he, hKind⟩ := hi.publication
  obtain ⟨f, hf, hKind'⟩ := hj.publication
  rw [Option.some.inj (he.symm.trans hf), hKind'] at hKind
  exact ⟨rfl, (Option.some.inj hKind).symm⟩

/-- Matching the terminal correction ordinal to the completed producer count selects that
lane's unique final publication and its actual released generation. -/
private theorem terminalFinalPeerAtWaitOfExitedCount {g wait : Nat} {stage : Fin 2}
    (terminal : CorrectionWaits X (g,wait) .terminal stage) (hPass : wait+1 < (X.tr g).length)
    (hExit : Exited X (terminalStatsProducer l g stage))
    (hCount : let producer := terminalStatsProducer l g stage
      observedBarrierOrdinal X (g, wait) (statsBarrierId l g stage) + 1 =
        (Scores.before X (producer, (X.tr producer).length)).notices) :
    ∃! pos, TerminalPeer l X g stage wait pos .final := by
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  have hWarp := terminalStatsProducerWarp hp g stage
  have hw : warpIndex l producer < 8 := hWarp ▸ warp.isLt
  have hId : 3 + warpIndex l producer = id :=
    (congrArg (3 + ·) hWarp).trans (terminalStatsBarrier l g stage)
  obtain ⟨pos, round, hPeer⟩ := terminalPeerAtWaitOfExitedExtent hp hX terminal hPass
    (fun _ => by have h := hCount; dsimp only at h; omega)
  obtain ⟨j, hIndex, hFinal⟩ := Scores.finalPublicationOfExit hp hX hPeer.publication hExit
  have hBefore : (Scores.before X (producer,pos)).notices =
      observedBarrierOrdinal X (g, wait) id := by
    rw [Scores.notificationOrdinal hp hX hw, Scores.observedOrdinal, hId]
    exact hPeer.ordinal
  have hAfter := Scores.noticesThroughFinal hX hFinal
  have hEq : pos = j := by
    by_contra hNe
    have hLt : pos < j := hIndex.lt_of_ne hNe
    have h := Scores.publicationOrdinalIncreases hp hX hPeer.publication hLt
    rw [← Scores.notificationOrdinal hp hX hw, ← Scores.notificationOrdinal hp hX hw] at h
    change (Scores.before X (producer,pos)).notices <
      (Scores.before X (producer,j)).notices at h
    change observedBarrierOrdinal X (g, wait) id + 1 =
      (Scores.before X (producer, (X.tr producer).length)).notices at hCount
    change (Scores.before X (producer, (X.tr producer).length)).notices =
      (Scores.before X (producer,j)).notices + 1 at hAfter
    omega
  subst j
  let peer : TerminalPeer l X g stage wait pos .final := { hPeer with publication := hFinal }
  exact ⟨pos, peer, fun _ h => (TerminalPeer.unique hp hX h peer).1⟩

/-- An exited active producer's final publication is the unique peer in the
terminal correction wait's generation. -/
theorem terminalFinalPeerOfActiveWait (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {g wait : Nat} {stage : Fin 2} (hWork : g/l.block < tilePrefix p p.batch * p.heads)
    (terminal : CorrectionWaits X (g,wait) .terminal stage) (hPass : wait+1 < (X.tr g).length)
    (hExit : Exited X (terminalStatsProducer l g stage)) :
    ∃! pos, TerminalPeer l X g stage wait pos .final := by
  let producer := terminalStatsProducer l g stage
  have hSame : producer / l.block = g / l.block := terminalStatsCta hp g stage
  have hW : warpIndex l producer < 8 :=
    (terminalStatsProducerWarp hp g stage).symm ▸ (terminalStatsWarp l g stage).isLt
  obtain ⟨batch,hb,hLo,hHi,hOrd⟩ :=
    terminalWaitOrdinalOfTrips hp hX hWork hUsedK terminal
  rw [correctionBarrierOrdinal] at hOrd
  obtain ⟨index,stop,hGet,hKind⟩ := hExit
  have hg := Step.CtaBar.thread_lt_of_get hX hGet
  obtain ⟨picked,hPicked,hPLo,hPHi,_,hNotice⟩ := Softmax.exitedActivePublicationCount
    hp hX hg hW (hSame.symm ▸ hWork) hCuQ hUsedK hGet hKind
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hBatch : picked = batch :=
    (hUnique picked ⟨hPicked,hSame ▸ hPLo,hSame ▸ hPHi⟩).trans
      (hUnique batch ⟨hb,hLo,hHi⟩).symm
  apply terminalFinalPeerAtWaitOfExitedCount hp hX terminal hPass ⟨index,stop,hGet,hKind⟩
  change observedBarrierOrdinal X (g,wait) (statsBarrierId l g stage) + 1 =
    (Scores.before X (producer,(X.tr producer).length)).notices
  rw [hBatch,hSame] at hNotice
  exact (congrArg (·+1) hOrd).trans hNotice.symm

/-- An exited active producer's final publication is the unique peer in the
terminal correction wait's generation. -/
theorem terminalFinalPeerOfActiveExit (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {store : EvId} {stage : Fin 2} {wait : Nat} {sum max : List (Option Byte)}
    (hWork : store.1 / l.block < tilePrefix p p.batch * p.heads)
    (hReads : Thread.Correction.TerminalLseReads l X store stage wait sum max)
    (hExit : Exited X (terminalStatsProducer l store.1 stage)) :
    ∃! pos, TerminalPeer l X store.1 stage wait pos .final :=
  terminalFinalPeerOfActiveWait hp hX hCuQ hUsedK hWork hReads.terminal
    (waitArrival hp hX hReads).2 hExit

/-- A terminal correction wait matches its exited producer's unique final publication. -/
theorem terminalFinalPeerOfExit (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {store : EvId} {stage : Fin 2} {wait : Nat} {sum max : List (Option Byte)}
    (hReads : Thread.Correction.TerminalLseReads l X store stage wait sum max)
    (hExit : Exited X (terminalStatsProducer l store.1 stage)) :
    ∃! pos, TerminalPeer l X store.1 stage wait pos .final := by
  have hWork := terminalStatsWaitHasWork hp hX hReads.terminal
  exact terminalFinalPeerOfActiveExit hp hX hCuQ hUsedK hWork hReads hExit

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
