-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemScoreToProbabilityAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityScoreOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
import Lemmas.Protocol.StagingHandoff
import Lemmas.Protocol.UnitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier PTX.TcMma Thread Thread.Scores

/-- A QK issue preceding a PV read of the same probability cell is complete before
the PV issue. The intervening packet observes a softmax release whose score acquisition
in turn observes a notification tracking the QK fragment. -/
theorem scoreDoneBeforeProbabilityOperand {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : CorrectionJointGuards l X) (stage : Fin 2) {writer reader : EvId}
    {cell : Cell} (hWrite : X.MmaCell writer cell)
    (hQk : MmaAccumulatorOn X writer cell (.probability stage))
    (hPv : MmaAOnProbabilityStage X reader cell stage) (hEarlier : writer.2 < reader.2) :
    DoneBefore l X writer reader := by
  let cta := reader.1/l.block
  let obj := probabilityObject l cta stage 0
  obtain ⟨wait,hWait⟩ := scoreToPvGuard hp hX stage hWrite hQk hPv hEarlier
  obtain ⟨_,phase,r,hr,hId,hOk,hPhase,hCount⟩ := probabilityAcquireRecord hp hX hWait.acquire
  obtain ⟨credit,hCredit,hSoft,hOrdinal,hObserved⟩ :=
    jointPollObservesSoftmax hp hX hGuard stage hr hOk hPhase
  rw [hId] at hObserved
  obtain ⟨k,_,scorePhase,s,hs,hScoreId,hScoreOk,hResume,hScorePhase,hLower⟩ :=
    scoreObservedBeforeSoftmaxCredit hp hX stage 0 hSoft hCredit
  obtain ⟨commit,spec,rank,hScore,hCommitOrdinal,hScoreObserved⟩ :=
    scoreCommitOfObservation hp hX stage hs hScoreOk hScorePhase
  rw [hScoreId] at hScoreObserved
  have hAcquire :=
    scoreAcquireOfRecord hp hX (wait := (credit.1,k)) stage hSoft hs hScoreId hScoreOk
  have hObservedScore := hAcquire.observes hScoreObserved
  have hObservedCredit := hWait.acquire.observes hObserved
  obtain ⟨d,op,acc,mask,_,_,hIssue,_⟩ := hWrite
  have hWriterCta : writer.1/l.block = cta := by
    unfold cta
    rw [hWait.afterIssue.1,hWait.returns.1.1]
  have hProducerCta := (probabilityCreditRole hp hX stage 0 hCredit).1
  obtain ⟨_,_,hReaderGet,_⟩ := hWait.acquire
  obtain ⟨_,_,hProducerGet,_⟩ := hAcquire
  have hScope : SameCta l credit.1 wait.1 :=
    ⟨event_thread_lt hX (e := (credit.1,k)) hProducerGet,event_thread_lt hX hReaderGet,
      hProducerCta.trans (congrArg (· / l.block) hWait.returns.1.1).symm⟩
  have hWriterScope : SameCta l writer.1 credit.1 :=
    ⟨hWait.afterIssue.1 ▸ event_thread_lt hX hReaderGet,
      event_thread_lt hX (e := (credit.1,k)) hProducerGet,
      hWriterCta.trans hProducerCta.symm⟩
  have hRelease : MbarRelease X credit obj .cta := ⟨0,1,hCredit⟩
  have hCausal := Staging.baseCausality_of_handoff (e := (credit.1,k)) hRelease hObservedCredit
    (MbarRing.Unit.Gate.scopesMeet hScope .cta .cta)
    ⟨rfl,hResume.1.2.1.le⟩ hWait.returns.1
  have hBefore := hWait.beforeCommit hScore (by rw [hCommitOrdinal]; omega)
  have hLane := mmaAndScoreCommitSameThread hp hX hIssue hScore hWriterCta
  have hTracks : TracksMma X writer commit :=
    ⟨hLane,hBefore,.inl ⟨d,op,acc,mask,hIssue⟩,spec,hScore.1⟩
  exact .inl ⟨(credit.1,k),.cta,
    ⟨_,_,⟨commit,spec,rank,rfl,hTracks,hScore.1,hScore.2,hScoreObserved.1⟩,hObservedScore⟩,
    MbarRing.Unit.Gate.scopesMeet hWriterScope .cluster .cta,hCausal⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
