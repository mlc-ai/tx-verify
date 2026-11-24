-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreLoadSources
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScorePollOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReuseTrace
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityStoreScoreOrder
import Lemmas.Protocol.UnitHandoff
import Lemmas.Protocol.UnitGate
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier PTX.TcMma Thread Thread.Scores Prologue

/-- The score commit and successful wait of an observed score load. -/
structure ScoreLoadScore (l : Launch) (X : Execution) (load : EvId) (stage : Fin 2) where
  wait : EvId
  commit : EvId
  spec : TcCommit.Spec
  rank : Fin 16
  score : ScoreCommit l X commit (load.1/l.block) stage spec rank
  notified : rank ∈ X.tcNotified commit
  observed : WaitObserves X (.async commit (.tcNotify rank)) wait
    (scoreReadyObject l (load.1/l.block) stage) true .cta
  resumed : Resumes kernel X wait load
  generation : scoreCommitOrdinal l X (load.1/l.block) stage commit =
    probabilityOrdinal l X (load.1/l.block) stage 0 load
  softmax : warpIndex l load.1 < 8
  stageMatches : warpIndex l load.1/4 = stage.val

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The load's actual acquire observes the score generation selected by its lane. -/
theorem scoreLoadObservesScore (hJoint : CorrectionJointGuards l X) {load : EvId} {cell : Cell}
    {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage) :
    Nonempty (ScoreLoadScore l X load stage) := by
  obtain ⟨hN,hWarp,hStage,hAcquire,hResume⟩ := hLoad.acquire hp hX
  obtain ⟨commit,spec,rank,hScore,hGen,hObserve⟩ :=
    scorePollObservesExactCommit hp hX hJoint stage rfl hWarp hStage hN
  exact ⟨⟨_,commit,spec,rank,hScore,hObserve.1,hAcquire.observes hObserve,hResume,
    hGen,hWarp,hStage⟩⟩

/-- The latest successful store guard observes the exact score generation of the store. -/
theorem probabilityStoreObservesLatestScore (hJoint : CorrectionJointGuards l X) {store : EvId}
    {cell : Cell} (stage : Fin 2) (hStore : StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.probability stage)) :
    ∃ seen : ProbabilityStoreScore l X store stage,
      scoreCommitOrdinal l X (store.1/l.block) stage seen.commit+1 =
        okPolls (scoreReadyObject l (store.1/l.block) stage) ((X.tr store.1).take store.2) := by
  let cta := store.1/l.block
  let object := scoreReadyObject l cta stage
  have hGroup := hFoot.warpGroup
  have hStage : warpIndex l store.1/4 = stage.val := by
    change store.1%l.block/128 = stage.val at hGroup
    unfold warpIndex
    omega
  have hWarp : warpIndex l store.1 < 8 := by have := stage.isLt; omega
  obtain ⟨wait,_,_,_,_,_,_,_,hAcquire,hResume,_,hP,hN,hWait⟩ :=
    probabilityStoreScoreRecordWithCursor hp hX stage hStore hFoot
  let n := okPolls object ((X.tr store.1).take store.2)-1
  obtain ⟨commit,spec,rank,hScore,hOrdinal,hObs⟩ :=
    scorePollObservesExactCommit hp hX hJoint (n := n) stage rfl hWarp hStage hN
  rw [← hWait] at hObs
  have hCur : scoreCommitOrdinal l X cta stage commit+1 =
      okPolls object ((X.tr store.1).take store.2) := by
    rw [hOrdinal]
    exact Nat.sub_add_cancel hP
  exact ⟨⟨wait,commit,spec,rank,hScore,hObs.1,hAcquire.observes hObs,hResume,hCur.ge⟩,hCur⟩

/-- An MMA tracked by the score commit has completed before the load. -/
theorem ScoreLoadScore.doneBeforeEarlierMma {mma load : EvId} {stage : Fin 2}
    (seen : ScoreLoadScore l X load stage) {d : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} (hMma : X.MmaIssue mma d op acc mask) (hCta : SameCta l mma.1 load.1)
    (hEarlier : mma.2 < seen.commit.2) : DoneBefore l X mma load := by
  have hIssuer := mmaAndScoreCommitSameThread hp hX hMma seen.score hCta.2.2
  have hTracks : TracksMma X mma seen.commit := ⟨hIssuer,hEarlier,
    .inl ⟨d,op,acc,mask,hMma⟩,seen.spec,seen.score.1⟩
  have hScope : SameCta l mma.1 seen.wait.1 := seen.resumed.1.1 ▸ hCta
  obtain ⟨_,_,he⟩ := seen.observed.1
  have hResume := seen.resumed.1
  have hPo := po_of_source_not_access hResume.1 hResume.2.1 hResume.2.2 (by rw [he]; rfl)
  exact .inl ⟨seen.wait,.cta,
    ⟨_,_,⟨seen.commit,seen.spec,seen.rank,rfl,hTracks,seen.score.1,
      seen.score.2,seen.notified⟩,seen.observed⟩,
    MbarRing.Unit.Gate.scopesMeet hScope .cluster .cta,.single (.inl hPo)⟩

/-- A subsequent QK issue observes the joint credit after this score load's wait. -/
theorem scoreLoadBeforeGuardedMma (hJoint : CorrectionJointGuards l X) {load mma wait : EvId}
    {cell : Cell} {stage : Fin 2} (hLoad : ScoreLoadCell l X load cell stage)
    (seen : ScoreLoadScore l X load stage) {d : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} (hMma : X.MmaIssue mma d op acc mask) (hSame : SameCta l mma.1 load.1)
    (hLater : seen.commit.2 ≤ mma.2) (hAcquire : MmaProbabilityAcquire l X mma stage 0 wait) :
    WaitBefore l X .waitLd load mma := by
  let cta := load.1/l.block
  let object := probabilityObject l cta stage 0
  have hCta := hSame.2.2
  have hCount := scoreCommitCountBeforeMma hp hX hMma seen.score hCta hLater
  obtain ⟨i,phase,poll,hPoll,hId,hSuccess,hPhase,hBudget⟩ := hAcquire.record hp hX
  rw [hCta] at hPoll hPhase hBudget
  change scoreCommitOrdinal l X cta stage mma ≤ phase+1 at hBudget
  change scoreCommitOrdinal l X cta stage seen.commit+1 ≤
    scoreCommitOrdinal l X cta stage mma at hCount
  have hWithin : probabilityOrdinal l X cta stage 0 load ≤ phase := by
    rw [← seen.generation]
    change scoreCommitOrdinal l X cta stage seen.commit ≤ phase
    omega
  obtain ⟨credit,hCredit,hLane,hGeneration,hObserve⟩ := jointPollObservesLane hp hX hJoint
    stage rfl seen.softmax seen.stageMatches hPoll hSuccess hPhase
  have hAcquire' : ScoreAcquire X wait object := by
    obtain ⟨e,q,he,hKind⟩ := hAcquire.event
    rw [hCta] at hKind
    exact ⟨e,q,he,hKind⟩
  rw [hId] at hObserve
  have hWaitCta : SameCta l credit.1 wait.1 := by
    rw [hLane,hAcquire.resume.1.1]
    exact ⟨hSame.2.1,hSame.1,hCta.symm⟩
  have hRelease : MbarRelease X credit object .cta := ⟨0,1,hCredit⟩
  have hHandoff := Staging.baseCausality_of_handoff (e := credit) hRelease
    (hAcquire'.observes hObserve) (MbarRing.Unit.Gate.scopesMeet hWaitCta .cta .cta)
    ⟨rfl,le_rfl⟩ hAcquire.resume.1
  exact hLoad.waitThroughCredit hp hX hCredit hLane (hGeneration.symm ▸ hWithin) hHandoff

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
