-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
public import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
public import Lemmas.Protocol.PollIndex
import Lemmas.Order.OrderBaseCausality
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.AsyncCopy PTX.TcMma Thread Thread.Scores

/-- The recorded acquire and score notification used by an actual probability store. -/
structure ProbabilityStoreScore (l : Launch) (X : Execution) (store : EvId)
    (stage : Fin 2) where
  wait : EvId
  commit : EvId
  spec : TcCommit.Spec
  rank : Fin 16
  score : ScoreCommit l X commit (store.1/l.block) stage spec rank
  notified : rank ∈ X.tcNotified commit
  observed : WaitObserves X (.async commit (.tcNotify rank)) wait
    (scoreReadyObject l (store.1/l.block) stage) true .cta
  resumes : Resumes kernel X wait store
  coversCursor : okPolls (scoreReadyObject l (store.1/l.block) stage)
    ((X.tr store.1).take store.2) ≤ scoreCommitOrdinal l X (store.1/l.block) stage commit + 1

/-- Every actual probability store observes an issued score commit of its stage. -/
theorem probabilityStoreObservesScore {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {store : EvId} {cell : Cell}
    (hStore : StoreCell l X store cell)
    (hFootprint : TensorStoreFootprint l store cell (.probability stage)) :
    Nonempty (ProbabilityStoreScore l X store stage) := by
  obtain ⟨w,i,phase,r,hr,hId,hOk,hPhase,hAcquire,hResume,hBound⟩ :=
    probabilityStoreScoreRecord hp hX stage hStore hFootprint
  obtain ⟨c,s,k,hScore,hOrdinal,hSeen⟩ := scoreCommitOfObservation hp hX stage hr hOk hPhase
  rw [hId] at hSeen
  exact ⟨⟨w,c,s,k,hScore,hSeen.1,hAcquire.observes hSeen,hResume,hOrdinal.symm ▸ hBound⟩⟩

/-- Every MMA tracked by the observed score commit is complete before the probability store. -/
theorem ProbabilityStoreScore.doneBefore {l : Launch} {X : Execution}
    {mma store : EvId} {stage : Fin 2} (h : ProbabilityStoreScore l X store stage)
    (hSame : SameCta l mma.1 store.1) (hTrack : TracksMma X mma h.commit) :
    DoneBefore l X mma store := by
  have hWaitCta : SameCta l mma.1 h.wait.1 := h.resumes.1.1 ▸ hSame
  have hResume := h.resumes.1
  obtain ⟨_,_,he⟩ := h.observed.1
  have hPo := po_of_source_not_access hResume.1 hResume.2.1 hResume.2.2 (by rw [he]; rfl)
  exact .inl ⟨h.wait,.cta,
    ⟨_,_,⟨h.commit,h.spec,h.rank,rfl,hTrack,h.score.1,h.score.2,h.notified⟩,h.observed⟩,
    MbarRing.Unit.Gate.scopesMeet hWaitCta .cluster .cta,.single (.inl hPo)⟩

/-- A real MMA on the same CTA that issued before the observed commit is complete
before the probability store. -/
theorem ProbabilityStoreScore.doneBeforeEarlierMma {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma store : EvId} {stage : Fin 2} (h : ProbabilityStoreScore l X store stage)
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op acc mask) (hSame : SameCta l mma.1 store.1)
    (hEarlier : mma.2 < h.commit.2) : DoneBefore l X mma store := by
  have hLane := mmaAndScoreCommitSameThread hp hX hMma h.score hSame.2.2
  exact h.doneBefore hSame ⟨hLane,hEarlier,.inl ⟨d,op,acc,mask,hMma⟩,h.spec,h.score.1⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
