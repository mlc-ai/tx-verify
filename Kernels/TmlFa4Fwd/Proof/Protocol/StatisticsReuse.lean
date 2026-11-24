-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Lemmas.Order.DependencyWitness
import Lemmas.Protocol.MbarRingRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Flow Thread Prologue

private theorem producerWarpOfPaired {l : Launch} {g h : Nat} {stage : Fin 2}
    (hPair : Paired l g h stage) : warpIndex l g < 8 := by
  have hLocal := Nat.mod_lt (warpIndex l h) (by decide : 0 < 4)
  have hStage := stage.isLt
  unfold Paired Correction.statsBarrierId at hPair
  omega

/-- With an actual peer publication in the correction credit's generation, the credit depends
on that producer's acquire of the indicated ordinal. -/
theorem creditDependsOnProducerAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j n : Nat} {credit : EvId} {key : Nat} {stage : Fin 2} {round : Scores.Round} {e : Event}
    (hSame : g/l.block = credit.1/l.block) (hPair : Paired l g credit.1 stage)
    (hPub : Scores.Publishes X (g,j) round) (hKey : CtaBarArrivalK l X (g,j) key)
    (he : X.get credit = some e) (hc : correctionAction e = some (.statsCredit stage))
    (hOrd : (Scores.before X (g,j)).barrier (3 + warpIndex l g) =
      (correctionBefore X credit).count (.statsCredit stage))
    (hN : n ≤ (correctionBefore X credit).count (.statsCredit stage)) :
    ∃ k, Scores.CreditAcquired X (g,k) ∧ (Scores.before X (g,k)).credits = n ∧
      Relation.TransGen (DepStep l kernel X) (.thread (g,k),true) (.thread credit,false) := by
  have hw := producerWarpOfPaired hPair
  obtain ⟨k, _, hAcquire, hCursor, hResume⟩ :=
    Scores.acquireBeforePublication hp hX hPub hw (hOrd ▸ hN)
  let warp : Fin 8 := ⟨warpIndex l g, hw⟩
  have hSources := statsBarrierSources hp hX warp
  have hShape := statsBarrierShape hp warp
  obtain ⟨_, ⟨f, hf, hKind, _, _⟩, _⟩ := Scores.publishes hp hX hPub
  have hPubKey := hSources.arrival_kind_key hX hShape ⟨f,hf,hKind⟩ hKey
  change key = 3 + warpIndex l g + 16 *
    observedBarrierOrdinal X (g,j) (3 + warpIndex l g) at hPubKey
  rw [← Scores.observedOrdinal, hOrd] at hPubKey
  obtain ⟨h, hWait, hCount, hPass, hReturn⟩ := namedWaitForCredit hp hX he hc
  obtain ⟨key', hk', hd⟩ := barrierSyncReturned hX hWait hPass
  have hPair' : 3 + warpIndex l g = Correction.statsBarrierId l credit.1 stage := hPair
  have hWaitKey := (hPair' ▸ hSources).arrival_kind_key hX (hPair' ▸ hShape) hWait
    (CtaBarK.arrival hk')
  change key' = Correction.statsBarrierId l credit.1 stage +
    16 * observedBarrierOrdinal X (credit.1,h) (Correction.statsBarrierId l credit.1 stage)
    at hWaitKey
  rw [hCount] at hWaitKey
  have hKeys : key' = key := hWaitKey.trans ((congrArg (fun id => id + 16 *
    (correctionBefore X credit).count (.statsCredit stage)) hPair').symm.trans hPubKey.symm)
  rw [hKeys] at hk' hd
  obtain ⟨ix,hCompleted⟩ := hd
  have hWitness := Witness.of_ctaBarCounted (e := (g,j)) (f := (credit.1,h))
    hk' hCompleted hKey hSame
  exact ⟨k, hAcquire, hCursor,
    ((Relation.TransGen.single (DepStep.of_resumes (L := l) hResume)).tail
      (DepStep.of_witness (L := l) hWitness)).tail (DepStep.of_resumes (L := l) hReturn)⟩

/-- Every correction credit has a participating producer in its observed named generation. -/
def CreditPeers (l : Launch) (X : Execution) : Prop :=
  ∀ stage credit e, X.get credit = some e → correctionAction e = some (.statsCredit stage) →
    ∃ producer round key, producer.1 / l.block = credit.1 / l.block ∧
      Paired l producer.1 credit.1 stage ∧ Scores.Publishes X producer round ∧
      CtaBarArrivalK l X producer key ∧
      (Scores.before X producer).barrier (3 + warpIndex l producer.1) =
        (correctionBefore X credit).count (.statsCredit stage)

/-- An exited representative of the producer warp has issued all notifications required by
the correction credit. A live representative needs no separate extent premise. -/
def ExitedCreditExtent (l : Launch) (X : Execution) : Prop :=
  ∀ stage credit e, X.get credit = some e → correctionAction e = some (.statsCredit stage) →
    ∃ g, g/l.block = credit.1/l.block ∧ Paired l g credit.1 stage ∧
      (Exited X g →
        (correctionBefore X credit).count (.statsCredit stage) <
          (Scores.before X (g,(X.tr g).length)).notices)

/-- Matching peer publications follow from the barrier history and the producer exit extent. -/
theorem creditPeersOfExitedExtent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hExtent : ExitedCreditExtent l X) : CreditPeers l X := by
  intro stage credit e he hc
  obtain ⟨g, hSame, hPair, hExited⟩ := hExtent stage credit e he hc
  have hW := producerWarpOfPaired hPair
  let w : Fin 8 := ⟨warpIndex l g, hW⟩
  let key := 3 + w.val
  let n := (correctionBefore X credit).count (.statsCredit stage)
  have eq : key = Correction.statsBarrierId l credit.1 stage := hPair
  have hS := statsBarrierSources hp hX w
  have hG := statsBarrierShape hp w
  obtain ⟨j, hWait, hCount, hPass, _⟩ := namedWaitForCredit hp hX he hc
  rw [← eq] at hWait hCount
  change observedBarrierOrdinal X (credit.1,j) key = n at hCount
  have hMember : warpIndex l g ∈ statsParticipants w := Finset.mem_insert_self ..
  have hWitness :
      ∃ pos mode, BarrierArrival X (g,pos) key (some 64) mode ∧
        observedBarrierOrdinal X (g,pos) key = n := by
    rw [← hCount]
    apply memberBarrierArrival hX hS hG hWait hPass hSame hMember
    intro hx
    obtain ⟨pos, hPub, hOrd⟩ := Scores.publicationAtOrdinal hp hX hW (hExited hx)
    exact ⟨pos, .arrive, hPub, hOrd.trans hCount.symm⟩
  obtain ⟨pos, mode, hPub, hOrd⟩ := hWitness
  obtain ⟨release, hRecorded, hDone⟩ := barrierSyncReturned hX hWait hPass
  have hKeyExact := hS.arrival_kind_key hX hG hWait (CtaBarK.arrival hRecorded)
  change release = key + 16 * observedBarrierOrdinal X (credit.1,j) key at hKeyExact
  rw [hCount] at hKeyExact
  have hIdBound : key < 16 := by unfold key; omega
  unfold CtaBarDone at hDone
  rw [hKeyExact, show (key+16*n)%16 = key by omega, show (key+16*n)/16 = n by omega] at hDone
  have hReleased' : CtaBarrier.Released l.block (X.barriers (g/l.block)) key
      (observedBarrierOrdinal X (g,pos) key) := by
    rw [hSame, hOrd]
    exact hDone
  have hKey := barrierArrivalKeyOfReleased hX hS hG hPub hReleased'
  obtain ⟨round, hPub'⟩ := Scores.publishesAtStatisticsBarrier hp hX hW
    (mode := mode) hPub
  refine ⟨(g,pos), round, _, hSame, hPair, hPub', hKey, ?_⟩
  rw [Scores.observedOrdinal]
  exact hOrd

private theorem stageOfPaired {l : Launch} {producer consumer : Nat} {stage : Fin 2}
    (h : Paired l producer consumer stage) : warpIndex l producer / 4 = stage.val := by
  have ha := Nat.mod_lt (warpIndex l consumer) (by decide : 0 < 4)
  unfold Paired Correction.statsBarrierId at h
  omega

/-- An actual correction credit is ordered after the corresponding acquires of its paired
producer, through the returned named wait. -/
def CreditAcquireDependencies (l : Launch) (X : Execution) : Prop :=
  ∀ stage credit e, X.get credit = some e → correctionAction e = some (.statsCredit stage) →
    ∀ n ≤ (correctionBefore X credit).count (.statsCredit stage),
      ∃ acquire, acquire.1/l.block = credit.1/l.block ∧
        Paired l acquire.1 credit.1 stage ∧ Scores.CreditAcquired X acquire ∧
        (Scores.before X acquire).credits = n ∧
        Relation.TransGen (DepStep l kernel X) (.thread acquire,true) (.thread credit,false)

/-- An exit counted by the matching statistics wait covers its correction credit ordinal. -/
def CountedExitCreditBound (l : Launch) (X : Execution) : Prop :=
  ∀ stage credit e, X.get credit = some e → correctionAction e = some (.statsCredit stage) →
    ∃ g, g/l.block = credit.1/l.block ∧ Paired l g credit.1 stage ∧
      ∀ j k stop,
        BarrierArrival X (credit.1,j) (Correction.statsBarrierId l credit.1 stage)
          (some 64) .sync →
        (correctionBefore X (credit.1,j)).barrier (Correction.statsBarrierId l credit.1 stage) =
          (correctionBefore X credit).count (.statsCredit stage) →
        Witness l X (.thread (g,k)) (credit.1,j) →
        X.get (g,k) = some stop → stop.kind = .exit →
        (correctionBefore X credit).count (.statsCredit stage) ≤ (Scores.before X (g,k)).notices

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A credit depends on its selected producer's earlier acquire through the matching named
barrier. A counted producer exit supplies the witness when its arrival was already consumed. -/
theorem creditDependsOnSelectedProducer {stage : Fin 2} {credit : EvId} {e : Event} {g n : Nat}
    (he : X.get credit = some e) (hc : correctionAction e = some (.statsCredit stage))
    (hSame : g / l.block = credit.1 / l.block) (hPair : Paired l g credit.1 stage)
    (hExtent : ∀ j k stop,
      BarrierArrival X (credit.1, j) (Correction.statsBarrierId l credit.1 stage)
        (some 64) .sync →
      (correctionBefore X (credit.1, j)).barrier (Correction.statsBarrierId l credit.1 stage) =
        (correctionBefore X credit).count (.statsCredit stage) →
      Witness l X (.thread (g, k)) (credit.1, j) →
      X.get (g, k) = some stop → stop.kind = .exit →
      (correctionBefore X credit).count (.statsCredit stage) ≤ (Scores.before X (g, k)).notices)
    (hN : n ≤ (correctionBefore X credit).count (.statsCredit stage)) :
    ∃ acquire, Scores.CreditAcquired X (g, acquire) ∧ (Scores.before X (g, acquire)).credits = n ∧
      Relation.TransGen (DepStep l kernel X) (.thread (g, acquire), true)
        (.thread credit, false) := by
  have hw := producerWarpOfPaired hPair
  let warp : Fin 8 := ⟨warpIndex l g, hw⟩
  let id := Correction.statsBarrierId l credit.1 stage
  have hId : 3+warp.val = id := hPair
  obtain ⟨j, hWait, hOrd, hPass, hResume⟩ := namedWaitForCredit hp hX he hc
  have hSrc := hId ▸ statsBarrierSources hp hX warp
  have hShape := hId ▸ statsBarrierShape hp warp
  have hMember : warpIndex l g ∈ statsParticipants warp := Finset.mem_insert_self ..
  obtain ⟨k, hWitness, hKind⟩ :=
    releasedMemberWitness hX hSrc hShape hWait hPass hSame hMember
  have hAcquire : ∃ a < k, Scores.CreditAcquired X (g,a) ∧
      (Scores.before X (g,a)).credits = n ∧ Resumes kernel X (g,a) (g,k) := by
    rcases hKind with ⟨mode, hArrival, hOrdinal⟩ | ⟨stop, hGet, hExit⟩
    · have hEq : id = 3 + warpIndex l g := hId.symm
      change BarrierArrival X (g,k) id (some 64) mode at hArrival
      rw [hEq] at hArrival
      obtain ⟨round, hp'⟩ := Scores.publishesAtStatisticsBarrier hp hX hw hArrival
      apply Scores.acquireBeforePublication hp hX hp' hw
      rw [Scores.observedOrdinal, ← hEq, hOrdinal, hOrd]
      exact hN
    · have hBefore : (correctionBefore X (credit.1, j)).barrier id =
          (correctionBefore X credit).count (.statsCredit stage) := by
        rw [correctionBarrierOrdinal]
        exact hOrd
      exact Scores.acquireBeforeExit hp hX hw hGet hExit
        (hN.trans (hExtent j k stop hWait hBefore hWitness hGet hExit))
  obtain ⟨a, _, hTake, hCount, hBefore⟩ := hAcquire
  exact ⟨a, hTake, hCount,
    ((Relation.TransGen.single (DepStep.of_resumes (L := l) hBefore)).tail
      (DepStep.of_witness (L := l) hWitness)).tail (DepStep.of_resumes (L := l) hResume)⟩

/-- A released named wait depends on a producer publication or the actual counted producer exit.
The exit case can use its terminal acquire at the final publication count. -/
theorem creditDependenciesOfCountedExitBound (hBound : CountedExitCreditBound l X)
    : CreditAcquireDependencies l X := by
  intro stage credit e he hc n hN
  obtain ⟨g, hSame, hPair, hExtent⟩ := hBound stage credit e he hc
  obtain ⟨a, hTake, hCount, hDep⟩ :=
    creditDependsOnSelectedProducer hp hX he hc hSame hPair hExtent hN
  exact ⟨(g, a), hSame, hPair, hTake, hCount, hDep⟩

/-- A producer publication at the matching generation also supplies the credit dependency. -/
theorem creditDependenciesOfPeers (hPeers : CreditPeers l X) : CreditAcquireDependencies l X := by
  intro stage credit e he hc n hN
  obtain ⟨⟨g,j⟩, round, key, hSame, hPair, hPub, hKey, hMatch⟩ := hPeers stage credit e he hc
  obtain ⟨k, hTake, hCount, hDep⟩ :=
    creditDependsOnProducerAcquire hp hX hSame hPair hPub hKey he hc hMatch hN
  exact ⟨(g,k), hSame, hPair, hTake, hCount, hDep⟩

/-- With participating peers through the credit frontier, continued publication proves release
of an earlier statistics generation. -/
theorem releasesBeforeReuseOfDependencies (hDeps : CreditAcquireDependencies l X) {g i j key : Nat}
    {initialRound nextRound : Scores.Round} (hInit : Scores.Publishes X (g,i) initialRound)
    (hKey : CtaBarArrivalK l X (g,i) key) (hNext : Scores.Publishes X (g,j) nextRound) (hLt : i < j)
    (hw : warpIndex l g < 8) :
    CtaBarDone l X (g / l.block) key := by
  classical
  let stage : Fin 2 := ⟨warpIndex l g/4, by omega⟩
  let cta := g/l.block
  let loc := Correction.statsCreditLoc l cta stage
  let gen := (Scores.before X (g,i)).barrier (3 + warpIndex l g)
  let n := gen+1
  have hN : n ≤ (Scores.before X (g,j)).barrier (3 + warpIndex l g) :=
    Scores.publicationOrdinalIncreases hp hX hInit hLt
  obtain ⟨k, -, hAcq, hOrd, _⟩ := Scores.acquireBeforePublication hp hX hNext hw hN
  let candidate (cursor : Nat) := ∃ event r, (X.objects loc)[cursor]? = some r ∧
    r.id = .thread event ∧ r.reply.waited = some true ∧ (Scores.before X event).credits = n ∧
    128*n ≤ MBarrier.unitsBefore (X.objects loc) cursor
  obtain ⟨pos, initial, hPos, hInitId, hSuccess, hUnits⟩ :=
    Correction.statsCreditUnitsOfAcquire hp hX stage rfl hAcq
  rw [hOrd] at hUnits
  have hExists : ∃ cursor, candidate cursor :=
    ⟨pos, (g,k), initial, hPos, hInitId, hSuccess, hOrd, hUnits⟩
  let cut := Nat.find hExists
  obtain ⟨_, _, hCut, _, _, _, hCover⟩ := Nat.find_spec hExists
  have hFrontier : CreditFrontier l X cta stage cut n := by
    intro index hEarly record credit hr hClean ha hId
    by_contra hLate
    have hOrdBound : n ≤ (correctionBefore X credit).count (.statsCredit stage) := by omega
    cases Correction.statsCreditHistorySource hp hX stage (List.mem_of_getElem? hr) with
    | init h => rw [ha] at h; cases h
    | poll h => rw [ha] at h; cases h
    | @credit source observed hSource he _ hc hOwner _ _ _ =>
      have hEq : source = credit := AsyncCopy.Ref.thread.inj (hSource.symm.trans hId)
      subst source
      obtain ⟨⟨a,poll⟩, hSame, hPair, hTake, hCount, hDep⟩ :=
        hDeps stage credit _ he hc n hOrdBound
      have hStage : stage.val = warpIndex l a / 4 := (stageOfPaired hPair).symm
      obtain ⟨pIndex, pRecord, hPollRecord, hPollId, hPassed, hEnough⟩ :=
        Correction.statsCreditUnitsOfAcquire hp hX stage hStage hTake
      change a/l.block = credit.1/l.block at hSame
      rw [hSame, hOwner] at hPollRecord hEnough
      have hpCandidate : candidate pIndex :=
        ⟨(a,poll), pRecord, hPollRecord, hPollId, hPassed, hCount, hCount ▸ hEnough⟩
      have hOrder := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hDep
      have hEarlier : pIndex ≤ index := by
        by_contra hLater
        exact hOrder ⟨index,pIndex,record,pRecord,hr,hId,hPollRecord,hPollId,by omega⟩
      exact Nat.find_min hExists (hEarlier.trans_lt hEarly) hpCandidate
  exact releasedByCreditFrontier hp hX hInit hKey rfl (Nat.lt_succ_self gen) hCover hFrontier

/-- The statistics barrier case of release before reuse, expressed through role observations. -/
theorem releasesStatsArrivalBeforeReuseOfDependencies (hDeps : CreditAcquireDependencies l X)
    {g i j key : Nat} {count nextCount : Option Nat} {mode : BarMode}
    (hRange : 3 ≤ key % 16 ∧ key % 16 < 11) (hKey : CtaBarArrivalK l X (g,i) key)
    (hInit : BarrierArrival X (g,i) (key % 16) count .arrive)
    (hNext : BarrierArrival X (g,j) (key % 16) nextCount mode) (hLt : i < j) :
    CtaBarDone l X (g / l.block) key := by
  obtain ⟨hId, hw, initialRound, hI⟩ := Scores.statisticsArrivalPublishes hp hX hRange hInit
  rw [hId] at hNext
  obtain ⟨nextRound, hJ⟩ := Scores.publishesAtStatisticsBarrier hp hX hw hNext
  exact releasesBeforeReuseOfDependencies hp hX hDeps hI hKey hJ hLt hw

theorem releasesStatsArrivalBeforeReuse (hPeers : CreditPeers l X) {g i j key : Nat}
    {count nextCount : Option Nat} {mode : BarMode} (hRange : 3 ≤ key % 16 ∧ key % 16 < 11)
    (hKey : CtaBarArrivalK l X (g,i) key) (hInit : BarrierArrival X (g,i) (key % 16) count .arrive)
    (hNext : BarrierArrival X (g,j) (key % 16) nextCount mode) (hLt : i < j) :
    CtaBarDone l X (g / l.block) key :=
  releasesStatsArrivalBeforeReuseOfDependencies hp hX (creditDependenciesOfPeers hp hX hPeers)
    hRange hKey hInit hNext hLt

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
