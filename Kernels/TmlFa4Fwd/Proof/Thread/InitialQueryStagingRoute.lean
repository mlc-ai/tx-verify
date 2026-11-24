-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryStatisticsTrace
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreCommitObservation
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOperandOutputOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
public import Kernels.TmlFa4Fwd.Proof.MmaFirstQueryOperand
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreSource
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress
import Kernels.TmlFa4Fwd.Proof.CorrectionStatsHandoff
import Kernels.TmlFa4Fwd.Proof.NamedBarrierParticipants
import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.AsyncCopy PTX.Flow Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem initialStatsBeforeStaging (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g store : Nat} {e : Event}
    (he : X.get (g, store) = some e) (hLater : 7988 < e.pc) (hLo : 8 ≤ warpIndex l g)
    (hHi : warpIndex l g < 12) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hUsedK : UsedKProtected p X) (stage : Fin 2) :
    ∃ wait < store, CorrectionWaits X (g, wait) .initial stage := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hThread : warpLane l g lane = g := Nat.sub_add_cancel
    ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have he' : X.get (warpLane l g lane, store) = some e := hThread.symm ▸ he
  have hg := event_thread_lt hX he
  obtain ⟨batch, hb, hlo, hhi, _, _, _, active, hActive⟩ :=
    Correction.correctionActiveTileOfEvent hp hX hg hLo hHi hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨_, _, hReach, hFirst, _, hSecond, _⟩ := Correction.correctionLaneBeforeRescaleOfEvent
    hp hX hb hlo hhi (active.checkpoint lane hl) hr hUsedK hActive.before hLater he'
  let pos := active.pos lane
  change pos + 6 ≤ store at hReach
  rw [hThread] at hFirst hSecond
  fin_cases stage
  · exact ⟨pos + 3, by omega, initialWaitObservation 0 hFirst⟩
  · exact ⟨pos + 5, by omega, initialWaitObservation 1 hSecond⟩

/-- An output staging store follows the actual initial statistics rendezvous of both Q banks. -/
theorem stageZeroStagingInitialStats (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g store : Nat} {a : Acc} {data : List Byte} (hStore : StageStagingWrite X (g, store) 0 a data)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads) (hUsedK : UsedKProtected p X)
    (stage : Fin 2) :
    ∃ wait < store, CorrectionWaits X (g, wait) .initial stage := by
  obtain ⟨box, chunk, hGet⟩ := hStore.decoded
  have hRange : 8492 ≤ Correction.outputStorePc 0 box chunk ∧
      Correction.outputStorePc 0 box chunk < 9205 := by
    fin_cases box <;> fin_cases chunk <;> decide
  have hHint : Correction.outputStorePc 0 box chunk ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX hGet
    (by change 173 < Correction.outputStorePc 0 box chunk; omega) hHint
  change roleBodyPc (warpIndex l g) (Correction.outputStorePc 0 box chunk) at hRole
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  exact initialStatsBeforeStaging hp hX hGet
    (by change 7988 < Correction.outputStorePc 0 box chunk; omega)
    hWarp.1 hWarp.2 hWork hUsedK stage

/-- A stage-zero staging store has already acquired its tile's first output completion. -/
theorem stageZeroStagingAcquire (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {data : List Byte} (hStore : StageStagingWrite X writer 0 a data) :
    ∃ wait, Correction.FirstOutputAcquire l X wait ∧ po X wait writer := by
  obtain ⟨box, chunk, hGet⟩ := hStore.decoded
  exact (Correction.StageZeroStagingWrites.of_event box chunk hGet).firstAcquire hp hX

/-- The selected softmax lane successfully acquired its initial score object. -/
@[no_expose] def InitialScoreWait (l : Launch) (X : Execution) (wait : EvId) (stage : Fin 2) :
    Prop :=
  X.get wait = some ⟨3425, .wait (firstScoreObject l (wait.1 / l.block) stage) 0 true true .cta⟩

/-- A returned initial statistics wait supplies the paired actual score-to-publication
route, even in a prefix in which some roles have yet to exit. -/
theorem firstScoreRouteToCorrectionOfWait (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g wait : Nat} {stage : Fin 2}
    (hStats : CorrectionWaits X (g,wait) .initial stage) (hPass : wait+1 < (X.tr g).length)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hCuQ : DrainCuQProtected p X)
    (hUsedK : UsedKProtected p X) :
    ∃ score scoreWait fence notice,
      SameCta l score g ∧ 3 + warpIndex l score = Correction.statsBarrierId l g stage ∧
      InitialScoreWait l X (score,scoreWait) stage ∧
      X.IsProxyFence (score,fence) (.async (some (.shared .cta))) none ∧
      Scores.Publishes X (score,notice) .first ∧ scoreWait < fence ∧ fence < notice := by
  let score := Correction.terminalStatsProducer l g stage
  let warp := Correction.terminalStatsWarp l g stage
  let id := Correction.statsBarrierId l g stage
  have hCta : score/l.block = g/l.block := Correction.terminalStatsCta hp g stage
  have hWarp : warpIndex l score = warp.val := Correction.terminalStatsProducerWarp hp g stage
  have hw : warpIndex l score < 8 := hWarp.symm ▸ warp.isLt
  have hId : 3+warp.val = id := Correction.terminalStatsBarrier l g stage
  have hBarId : 3+warpIndex l score = id := (congrArg (3+·) hWarp).trans hId
  have hMember : warpIndex l score ∈ statsParticipants warp := by
    rw [hWarp]
    exact Finset.mem_insert_self ..
  have hSources := statsBarrierSources hp hX warp
  have hSource := hId ▸ hSources
  have hShape := hId ▸ statsBarrierShape hp warp
  have hOrd := correctionInitialWaitOrdinal hp hX hStats hSource
  rw [correctionBarrierOrdinal] at hOrd
  obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := correctionWaits hp hX hStats
  have hArrive : BarrierArrival X (g,wait) id (some 64) .sync := ⟨e,he,hKind⟩
  obtain ⟨pos,mode,hPeer,hOrdinal⟩ := memberBarrierArrival hX hSource hShape
    hArrive hPass hCta hMember (fun hExit => by
      obtain ⟨exit,last,he,hExitKind⟩ := hExit
      obtain ⟨site,kind⟩ := last
      change kind = .exit at hExitKind
      subst kind
      rw [actualExitPc hX he] at he
      obtain ⟨_,_,notice,_,_,_,hPub,_,_⟩ :=
        firstScoreStatisticsOfExit hp hX hw (hCta.symm ▸ hWork) hCuQ hUsedK he
      have hPubOrd := Scores.firstOrdinal hp hX hPub ((congrArg (3+·) hWarp).symm ▸ hSources)
      rw [Scores.barrierOrdinal,hBarId] at hPubOrd
      obtain ⟨_,⟨event,hGet,hKind,_,_⟩,_⟩ := Scores.publishes hp hX hPub
      rw [hBarId] at hKind
      exact ⟨notice,.arrive,⟨event,hGet,hKind⟩,hPubOrd.trans hOrd.symm⟩)
  have hPeer' : BarrierArrival X (score,pos) (3+warpIndex l score) (some 64) mode :=
    hBarId.symm ▸ hPeer
  obtain ⟨round,hPub⟩ := Scores.publishesAtStatisticsBarrier hp hX hw hPeer'
  have hZero : (Scores.before X (score,pos)).notices = 0 := by
    rw [Scores.notificationOrdinal hp hX hw,Scores.barrierOrdinal,hBarId]
    exact hOrdinal.trans hOrd
  have hRound : round = .first := by
    by_contra hLater
    obtain ⟨earlier,hLt,source,hEvent,hNotice⟩ :=
      firstStatisticsOfLaterPublication hp hX hw (hCta.symm ▸ hWork) hCuQ hUsedK hLater hPub
    have hOnce : source ∈ (X.tr score).take pos := by
      apply List.mem_of_getElem? (i := earlier)
      rwa [List.getElem?_take_of_lt hLt]
    have hPos : 0 < ((X.tr score).take pos).countP Scores.publishesStats :=
      List.countP_pos_iff.mpr ⟨source,hOnce,by simp [Scores.publishesStats,hNotice]⟩
    rw [Scores.beforeNotices] at hZero
    exact Nat.not_lt_zero _ (hZero ▸ hPos)
  subst round
  obtain ⟨scoreWait,fence,notice,obj,hWait,hFence,hFirst,hBefore,hAfter⟩ :=
    firstScoreStatisticsOfPublication hp hX hw (hCta.symm ▸ hWork) hCuQ hUsedK hPub
  have hAddr := Softmax.firstScoreWaitAddress hp hX hWait
  have hStage : warpIndex l score/4 = stage.val := by
    unfold id Correction.statsBarrierId at hBarId
    have hMod := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    omega
  rw [hStage] at hAddr
  exact ⟨score,scoreWait,fence,notice,⟨event_thread_lt hX hWait,event_thread_lt hX he,hCta⟩,
    hBarId,by simpa only [InitialScoreWait,hAddr,firstScoreObject] using hWait,
    ⟨_,hFence⟩,hFirst,hBefore,hAfter⟩

private def afterInitialQk (stage : Fin 2) : Nat := Mma.qkPc (Mma.initialQkBlock stage) + 8

set_option maxRecDepth 100000 in
private theorem initialQkFloorCode (stage : Fin 2) :
    (kernel.code.drop (afterInitialQk stage)).all
      (fun i => staysPastEvent (afterInitialQk stage) i.op) = true := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem initialQkFloorSegments (stage : Fin 2) :
    Assumptions.swExp2Sites.all (fun pc =>
      match Assumption.cuteExp2.matchAt kernel pc with
      | some mat => decide (afterInitialQk stage ≤ mat.stop)
      | none => false) = true := by
  fin_cases stage <;> kernel_rfl

private theorem commitWarp (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e) (hLo : 2197 ≤ e.pc) (hHi : e.pc < 2768)
    : warpIndex l i.1 = 12 := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  rcases hRole with h | h
  · omega
  · split_ifs at h <;> omega

private theorem sameScoreAndOutputIssuer (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (block : Fin 4) {producer commit g output : Nat}
    {s spec : TcCommit.Spec}
    (hCommit : X.get (producer, commit) =
      some ⟨(Mma.commitSite (Mma.qkCommitSite block)).pc, .tc (.commit s)⟩)
    (hOutput : FirstOutputCommit X (g, output) spec) (hOwner : producer / l.block = g / l.block) :
    producer = g := by
  change X.get (g, output) = some ⟨2642, .tc (.commit spec)⟩ at hOutput
  let pc := (Mma.commitSite (Mma.qkCommitSite block)).pc
  have hBounds : 2197 ≤ pc ∧ pc < 2768 := by fin_cases block <;> decide
  have hScoreWarp := commitWarp hp hX hCommit hBounds.1 hBounds.2
  have hOutputWarp := commitWarp hp hX hOutput
    (by change 2197 ≤ 2642; decide) (by change 2642 < 2768; decide)
  have hWarp : SameWarp l producer g :=
    ⟨⟨event_thread_lt hX hCommit, event_thread_lt hX hOutput, hOwner⟩,
      hScoreWarp.trans hOutputWarp.symm⟩
  obtain ⟨_, _, leader, hElect, hFirst⟩ := Mma.scoreCommitLeader hp hX block hCommit
  obtain ⟨_, _, wanted, hElect', hLast⟩ := Mma.firstOutputCommitLeader hp hX hOutput
  exact sameWarp_eq_of_lane_eq hWarp
    (hFirst.trans ((Mma.sameLeader hX hWarp hElect hElect').trans hLast.symm))

/-- The first score producer and the actual stage-zero output committer use the same lane. -/
theorem firstQkOutputIssuer (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait : Nat}
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait) {final : EvId}
    {s : TcCommit.Spec} (hOutput : FirstOutputCommit X final s)
    (hOwner : producer / l.block = final.1 / l.block) : producer = final.1 := by
  obtain ⟨g, j⟩ := final
  exact sameScoreAndOutputIssuer hp hX (Softmax.firstQkBlock stage)
    hPhase.commitEvent hOutput hOwner

set_option maxRecDepth 100000 in
private theorem outputFloorCode :
    (kernel.code.drop 2642).all (fun i => staysPastEvent 2642 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem outputFloorSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match Assumption.cuteExp2.matchAt kernel pc with
      | some mat => decide (2642 ≤ mat.stop)
      | none => false) = true := by
  kernel_rfl

/-- An initial fragment on the actual stage-zero output issuer precedes its output commit. -/
theorem initialQueryFragmentBeforeOutputCommit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2}
    {mma final : EvId} {s : TcCommit.Spec} (hMma : Mma.InitialQueryFragment X stage mma)
    (hFinal : FirstOutputCommit X final s) (hLane : mma.1 = final.1) :
    mma.2 < final.2 := by
  obtain ⟨g, index⟩ := mma
  obtain ⟨other, finish⟩ := final
  change g = other at hLane
  subst other
  obtain ⟨step, _, _, _, _, hFragment⟩ := hMma
  have hStep := step.isLt
  exact traceOrderOfPcFloor hX outputFloorCode outputFloorSegments hFragment hFinal
    (by
      change Mma.qkPc (Mma.initialQkBlock stage) + step.val < 2642
      fin_cases stage
      · change 2197 + step.val < 2642; omega
      · change 2259 + step.val < 2642; omega)
    le_rfl

/-- The paired initial score acquire observes every initial Q fragment of its stage. The
actual output commit anchors the issuer to the same full-warp election as the score commit. -/
theorem InitialScoreWait.observesInitialQuery (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2} {wait mma final : EvId}
    {spec : TcCommit.Spec} (hWait : InitialScoreWait l X wait stage)
    (hOutput : FirstOutputCommit X final spec) (hMma : Mma.InitialQueryFragment X stage mma)
    (hLane : mma.1 = final.1) (hCta : final.1 / l.block = wait.1 / l.block) :
    AsyncObserved X mma .mmaDone wait true .cta ∧ SameCta l mma.1 wait.1 := by
  unfold InitialScoreWait at hWait
  obtain ⟨block, ⟨producer, commit⟩, s, rank, hCommit, hSame, hTarget, hRank, hObserve⟩ :=
    firstScoreWaitObservesCommit hp hX stage hWait
  obtain ⟨g, output⟩ := final
  let pc := (Mma.commitSite (Mma.qkCommitSite block)).pc
  have hActor := sameScoreAndOutputIssuer hp hX block hCommit hOutput
    (hSame.2.2.trans hCta.symm)
  subst producer
  obtain ⟨g', index⟩ := mma
  change g' = g at hLane
  subst g'
  obtain ⟨step, d, op, accum, mask, hFragment⟩ := hMma
  have hSite : pc ∈ fixedCommits := by fin_cases block <;> decide
  have hAddr := congrArg Loc.addr (Mma.mmaFixedCommitExactAddress hp hX hCommit hSite hTarget)
  change l.sharedBase + (80 + 8 * stage.val) = l.sharedBase + Mma.fixedMmaCommitOffset pc at hAddr
  have hPast : afterInitialQk stage ≤ pc := by
    fin_cases stage <;> fin_cases block <;> first | decide |
      simp [pc, Mma.qkCommitSite, Mma.commitSite, Mma.fixedMmaCommitOffset] at hAddr
  have hStep := step.isLt
  have hEarlier := traceOrderOfPcFloor hX (initialQkFloorCode stage) (initialQkFloorSegments stage)
    hFragment hCommit (show Mma.qkPc (Mma.initialQkBlock stage) + step.val < afterInitialQk stage
      by unfold afterInitialQk; omega) hPast
  have hIssue : X.Commit (g, commit) s := ⟨pc, hCommit⟩
  have hTracks : TracksMma X (g, index) (g, commit) :=
    ⟨rfl, hEarlier, .inl ⟨d, op, accum, mask, _, hFragment⟩, s, hIssue⟩
  exact ⟨⟨_, _, ⟨(g, commit), s, rank, rfl, hTracks, hIssue, hTarget, hRank⟩, hObserve⟩, hSame⟩

end PTX.Kernels.TmlFa4Fwd.Thread
