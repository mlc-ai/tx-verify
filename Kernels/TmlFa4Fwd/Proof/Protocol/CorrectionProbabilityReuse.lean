-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreStatisticsGate
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.MbarRingRound
public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsTripExtent
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy Thread Thread.Scores Correction Epilogue
open PTX.MBarrier hiding okPolls
open PTX.Kernels.TmlFa4Fwd.Prologue (warpIndex)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem scoreOfStatisticsPublication {g j cta n : Nat} {round : Round} (stage : Fin 2)
    (hw : warpIndex l g < 8) (hCta : g / l.block = cta) (hStage : warpIndex l g / 4 = stage.val)
    (hPub : Publishes X (g,j) round)
    (hN : n + (if round = .final then 1 else 0) < (before X (g,j)).notices + 1) :
    ∃ (a k phase : Nat) (r : Record Ref), (X.objects (scoreReadyObject l cta stage))[k]? = some r ∧
      r.id = .thread (g,a) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (scoreReadyObject l cta stage)) k = some phase ∧
      n ≤ phase ∧ Resumes kernel X (g,a) (g,j) := by
  let loc := scoreReadyObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hClean : ∀ r ∈ log, (∃ p ok, r.action = .pollParity p ok) → r.fault = none :=
    fun _ hr hs => actualInitOrPollClean hp hX hr (.inr hs)
  obtain ⟨k, ev, q, acq, sc, hGet, hKind, hOrdinal, hResume⟩ :=
    statisticsScoreAcquire hp hX stage hw hCta hStage hPub hN
  obtain ⟨source, kind⟩ := ev
  change kind = _ at hKind
  subst kind
  have hNth := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hNth
  have hLt : n < okPolls loc (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hNth]
    exact ⟨_,hGet⟩
  obtain ⟨i, r, _, hr, hid, _, hSuccess, _, hBefore⟩ := MbarRing.Poll.record hX hClean hLt
  rw [hNth] at hid
  have hSel := objectThreadSelected_iff.mpr ⟨_, hid⟩
  have hChecked := X.objects_checked hX loc
  have hAlt := scoreReadySelectedAlternates hp hX stage hw hCta hStage
  obtain ⟨s, hs, hLower, _⟩ :=
    hChecked.selected_poll_phase_ge hNo (objectThreadSelected g) (by decide) hAlt hr hSel hSuccess
  have hP : 0 < s.phase := by omega
  obtain ⟨st, q, hSt, _, _, hComplete⟩ := hChecked.okPoll hr hSuccess
  rw [hs] at hSt
  obtain rfl := Option.some.inj hSt
  have hPhase : observedAt log i = some (s.phase - 1) := by
    change (log[i]?).bind (·.reply.completed) = _
    rw [hr, Option.bind_some, hComplete, ite_eq_left hP]
  exact ⟨k,i,s.phase-1,r,hr,hid,hSuccess,hPhase,by omega,hResume⟩

/-- A correction credit coupled to a fresh statistics publication has an earlier successful
joint probability observation of at least its preceding generation. -/
theorem correctionCreditProbabilityGuardOfPublication {g : EvId} {cta atCredit pos : Nat}
    (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (probabilityObject l cta stage 0))[atCredit]? = some r)
    (hId : r.id = .thread g) (hCredit : ProbabilityCredit l X g cta stage 0)
    (hPos : 0 < probabilityOrdinal l X cta stage 0 g) {round : Round} (hFresh : round ≠ .final)
    (hPub : Publishes X (terminalStatsProducer l g.1 stage,pos) round)
    (hOrd : observedBarrierOrdinal X (terminalStatsProducer l g.1 stage,pos)
      (statsBarrierId l g.1 stage) = probabilityOrdinal l X cta stage 0 g)
    (hDep : Relation.TransGen (DepStep l kernel X)
      (.thread (terminalStatsProducer l g.1 stage,pos),false) (.thread g,false)) :
    let loc := probabilityObject l cta stage 0
    ∃ k w st, k < atCredit ∧ (X.objects loc)[k]? = some w ∧ w.reply.waited = some true ∧
      stateBefore (X.objects loc) k = some st ∧ probabilityOrdinal l X cta stage 0 g ≤
        st.phase := by
  let producer := terminalStatsProducer l g.1 stage
  let n := probabilityOrdinal l X cta stage 0 g
  let loc := probabilityObject l cta stage 0
  have hWarp := terminalStatsProducerWarp hp g.1 stage
  have hw := hWarp ▸ (terminalStatsWarp l g.1 stage).isLt
  have hCta := (terminalStatsCta hp g.1 stage).trans
    (probabilityCreditRole hp hX stage 0 hCredit).1
  have hs : warpIndex l producer / 4 = stage.val := by
    have hRow : rowOf l g.1 < 128 := Nat.mod_lt _ (by decide)
    rw [hWarp]
    change (rowOf l g.1 / 32 + 4 * stage.val) / 4 = stage.val
    omega
  have hNamed : 3 + warpIndex l producer = statsBarrierId l g.1 stage := by
    rw [hWarp]
    exact terminalStatsBarrier l g.1 stage
  have hRead : (before X (producer,pos)).notices = n := by
    rw [notificationOrdinal hp hX hw, barrierOrdinal, hNamed]
    exact hOrd
  have hN : n + (if round = .final then 1 else 0) < (before X (producer,pos)).notices + 1 := by
    simp [hFresh,hRead]
  obtain ⟨a,k,phase,w,hW,hWId,hOk,hSeen,hLower,hResume⟩ :=
    scoreOfStatisticsPublication hp hX stage hw hCta hs hPub hN
  obtain ⟨e,spec,rank,hCommit,hOrdinal,hObserved⟩ :=
    scoreCommitOfObservation hp hX stage hW hOk hSeen
  have hLess : n - 1 < scoreCommitOrdinal l X cta stage e := by
    change 0 < n at hPos
    omega
  obtain ⟨b,i,q,poll,hPoll,hPId,hPOk,hPResume,hPSeen,hPLower,_,_⟩ :=
    probabilityObservedBeforeScoreOrdinal hp hX hCommit 0 hLess
  obtain ⟨_,hGet⟩ := hCommit.1
  have hIssue : DepStep l kernel X (.thread e,false) (.async e (.tcNotify rank),false) :=
    DepStep.issue ⟨_,hGet⟩ hObserved.1 (by intro x h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  rw [hWId] at hObserved
  have hPath := ((((Relation.TransGen.single (DepStep.of_resumes l hPResume)).tail hIssue).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hObserved))).tail
    (DepStep.of_resumes l hResume)).trans hDep
  rw [← hPId, ← hId] at hPath
  have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hPath
  have hBefore : i < atCredit := by
    rcases Nat.lt_trichotomy i atCredit with h | rfl | h
    · exact h
    · obtain rfl := Option.some.inj (hPoll.symm.trans hr)
      obtain ⟨ref,source,parity,acq,scope,hRef,hWait⟩ := hX.wait_of_record hr hPOk
      have hSame := Ref.thread.inj (hRef.symm.trans hId)
      rw [hSame] at hWait
      obtain ⟨_,hGet⟩ := hCredit
      exact Kind.noConfusion (congrArg Event.kind (Option.some.inj (hGet.symm.trans hWait)))
    · exact (hNot ⟨atCredit,i,r,poll,hr,rfl,hPoll,rfl,h⟩).elim
  obtain ⟨st,hState,hPhase⟩ := (X.objects_checked hX loc).observed_phase hPoll hPOk hPSeen
  exact ⟨i,poll,st,hBefore,hPoll,hPOk,hState,by omega⟩

/-- Each positive joint correction credit has the actual probability guard for its local
generation. The selected tile geometry aligns both sides of the statistics rendezvous. -/
theorem correctionJointGuardsOfCuQ (hCuQ : DrainCuQProtected p X) : CorrectionJointGuards l X := by
  intro cta atCredit r credit stage log hr hId hCredit hRole hPositive
  obtain ⟨g,i⟩ := credit
  let n := probabilityOrdinal l X cta stage 0 (g,i)
  let producer := terminalStatsProducer l g stage
  let warp := terminalStatsWarp l g stage
  let id := statsBarrierId l g stage
  have hId' : 3 + warp.val = id := terminalStatsBarrier l g stage
  have hWarp := terminalStatsProducerWarp hp g stage
  have hw : warpIndex l producer < 8 := hWarp ▸ warp.isLt
  have hMember : warpIndex l producer ∈ statsParticipants warp := by
    rw [hWarp]
    exact Finset.mem_insert_self ..
  have hNamed : 3 + warpIndex l producer = id := (congrArg (3 + ·) hWarp).trans hId'
  have hCta := terminalStatsCta hp g stage
  have hOwner := (probabilityCreditRole hp hX stage 0 hCredit).1
  have hCta' : producer / l.block = cta := hCta.trans hOwner
  have hSources := hId' ▸ statsBarrierSources hp hX warp
  have hShape := hId' ▸ statsBarrierShape hp warp
  have hUsedK := usedKProtected hp hX
  rcases correctionProbabilityCreditStatsWait hp hX stage hRole hCredit with
    ⟨hZero,_⟩ | ⟨j,hOrder,hWait,hCount⟩
  · exact (Nat.ne_of_gt hPositive hZero).elim
  change BarrierArrival X (g,j) id (some 64) .sync at hWait
  change (correctionBefore X (g,j)).barrier id = n at hCount
  obtain ⟨picked,round,hRound,hEq⟩ := correctionWaitOfStatisticsSync hp hX
    (show 3 ≤ id ∧ id < 11 by rw [← hId']; have := warp.isLt; omega) hWait
  have hStage : stage = picked := by
    apply Fin.ext
    change statsBarrierId l g stage = statsBarrierId l g picked at hEq
    unfold statsBarrierId at hEq
    omega
  subst picked
  have hOrdinal : observedBarrierOrdinal X (g,j) id = n :=
    (correctionBarrierOrdinal X (g,j) id).symm.trans hCount
  have hWork : g / l.block < tilePrefix p p.batch * p.heads :=
    statsWaitHasWork hp hX hRound
  have hBounds : ∃ batch, batch < p.batch ∧
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (n ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) ∧
      (round = .rescale → n < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) ∧
      (round = .terminal → TerminalProbabilityCredit l X (g,i) cta stage) ∧
      round ≠ .initial := by
    cases round with
    | initial =>
      have hZero := correctionInitialWaitOrdinal hp hX hRound hSources
      rw [hCount] at hZero
      exact (Nat.ne_of_gt hPositive hZero).elim
    | rescale =>
      obtain ⟨b,hB,hLo,hHi,hTrip⟩ :=
        rescaleWaitOrdinalBeforeTerminal hp hX hWork hUsedK hRound
      rw [hCount] at hTrip
      exact ⟨b,hB,hLo,hHi,hTrip.le,fun _ => hTrip,(by intro h; cases h),by decide⟩
    | terminal =>
      obtain ⟨b,hB,hLo,hHi,hTrip⟩ :=
        terminalWaitOrdinalOfTrips hp hX hWork hUsedK hRound
      rw [hCount] at hTrip
      exact ⟨b,hB,hLo,hHi,hTrip.le,(by intro h; cases h),
        fun _ => terminalProbabilityCreditAfterStats hp hX stage hRole hCredit hRound hOrder,
        by decide⟩
  obtain ⟨batch,hb,hLo,hHi,hTrip,hStrict,hTerminal,hNotInitial⟩ := hBounds
  have hCreditGet := hCredit
  obtain ⟨_,he⟩ := hCreditGet
  have hI : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hPass : j+1 < (X.tr g).length := by omega
  obtain ⟨pos,mode,hArrival,hGen⟩ := memberBarrierArrival hX hSources hShape
    hWait hPass hCta hMember (by
      rintro ⟨exit,stop,hGet,hExit⟩
      have hExtent := Statistics.ordinalBeforeActiveExit hp hX hCuQ hUsedK
        (ordinal := n) hw (hCta.symm ▸ hWork) hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi)
        (by rw [hCta]; exact hTrip) hGet hExit
      have hMono : (before X (producer,exit)).notices ≤
          (before X (producer,(X.tr producer).length)).notices := by
        have hLt : exit < (X.tr producer).length := (List.getElem?_eq_some_iff.mp hGet).1
        rw [beforeNotices,beforeNotices]
        exact countP_take_mono _ _ hLt.le
      obtain ⟨pos,hArrival,hOrd⟩ := publicationAtOrdinal hp hX hw (hExtent.trans_le hMono)
      rw [hNamed] at hArrival hOrd
      exact ⟨pos,.arrive,hArrival,hOrd.trans hOrdinal.symm⟩)
  have hObserved : BarrierArrival X (producer,pos) (3 + warpIndex l producer) (some 64) mode := by
    rw [hNamed]
    exact hArrival
  obtain ⟨publication,hPub⟩ := publishesAtStatisticsBarrier hp hX hw hObserved
  have hPubOrdinal : observedBarrierOrdinal X (producer,pos) id = n := hGen.trans hOrdinal
  by_cases hFinal : publication = .final
  · subst publication
    have hNotices : (before X (producer,pos)).notices = n := by
      rw [notificationOrdinal hp hX hw,barrierOrdinal,hNamed]
      exact hPubOrdinal
    obtain ⟨selected,hS,hSLo,hSHi,hBefore⟩ :=
      Softmax.finalPublicationOrdinalLower hp hX hw (hCta.symm ▸ hWork) hCuQ hUsedK hPub
    obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
    have hBatch : selected = batch :=
      (hUnique selected ⟨hS,hCta ▸ hSLo,hCta ▸ hSHi⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
    rw [hBatch,hCta,hNotices] at hBefore
    have hTerminalRound : round = .terminal := by
      cases round with
      | initial => exact (hNotInitial rfl).elim
      | rescale => exact ((hStrict rfl).not_ge hBefore).elim
      | terminal => rfl
    have hStageWarp : warpIndex l producer / 4 = stage.val := by
      have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
      rw [hWarp]
      change (rowOf l g / 32 + 4 * stage.val) / 4 = stage.val
      omega
    let prev := n - 1
    have hPositive' : 0 < n := hPositive
    have hScoreBudget : prev + (if Round.final = .final then 1 else 0) <
        (before X (producer,pos)).notices + 1 := by
      simp only [ite_true,hNotices]
      omega
    obtain ⟨_,k,phase,w,hW,_,hOk,hSeen,hLower,_⟩ :=
      scoreOfStatisticsPublication hp hX stage hw hCta' hStageWarp hPub hScoreBudget
    obtain ⟨score,spec,rank,hScore,hEq,_⟩ := scoreCommitOfObservation hp hX stage hW hOk hSeen
    exact terminalCorrectionProbabilityGuard hp hX hr hId hCredit
      (hTerminal hTerminalRound) hScore (hEq ▸ hLower)
  · obtain ⟨key,hKey,hDone⟩ := barrierSyncReturned hX hWait hPass
    have hKeyExact := hSources.arrival_kind_key hX hShape hWait hKey.arrival
    change key = id + 16 * observedBarrierOrdinal X (g,j) id at hKeyExact
    have hRem : key % 16 = id := by have := hShape.id_lt; omega
    have hQuot : key / 16 = observedBarrierOrdinal X (g,j) id := by
      have := hShape.id_lt
      omega
    have hReleased : CtaBarrier.Released l.block (X.barriers (producer / l.block)) id
        (observedBarrierOrdinal X (producer,pos) id) := by
      rw [hCta,hGen]
      change CtaBarrier.Released l.block (X.barriers (g / l.block)) (key % 16) (key / 16)
        at hDone
      rwa [hRem,hQuot] at hDone
    have hArrivalKey := barrierArrivalKeyOfReleased hX hSources hShape hArrival hReleased
    rw [hGen,← hKeyExact] at hArrivalKey
    obtain ⟨finish,hComplete⟩ := hDone
    have hWitness := Witness.of_ctaBarCounted hKey hComplete hArrivalKey hCta
    have hResume : Resumes kernel X (g,j) (g,i) := by
      obtain ⟨e,hGet,hKind⟩ := hWait
      apply Resumes.of_blocking (f := (g,i)) hGet (b := false) ?_ ⟨rfl,hOrder,hI⟩
      rw [hKind]
      rfl
    have hDep := (Relation.TransGen.single (DepStep.of_witness l hWitness)).tail
      (DepStep.of_resumes l hResume)
    exact correctionCreditProbabilityGuardOfPublication hp hX stage hr hId hCredit
      hPositive hFinal hPub hPubOrdinal hDep

/-- Both joint probability histories are fault-free with the protected query geometry. -/
theorem jointProbabilityHistoryNoFaultOfCuQ (hCuQ : DrainCuQProtected p X) {cta : Nat}
    (stage : Fin 2) {r : Record Ref} (hr : r ∈ X.objects (probabilityObject l cta stage 0)) :
    r.fault = none :=
  jointProbabilityHistoryNoFault hp hX (correctionJointGuardsOfCuQ hp hX hCuQ) stage hr

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
