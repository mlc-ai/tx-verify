-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CachePublicationOutput
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInitialValueGroup
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialValueStaging
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePhase

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy
open Thread.Loader (PrimingValueVector PublishedCopyGroup readyObject)

/-- A second-stage correction write forces the ordinal-zero publication that
contains every actual priming V vector of its CTA. -/
theorem primingValuePublicationOfSecondStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy writer : EvId} {pair : Fin 16} {upper : Bool} {s : Spec} {a : Acc} {data : List Byte}
    (hCopy : PrimingValueVector X copy pair upper s)
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hSame : copy.1 / l.block = writer.1 / l.block) :
    ∃ publication, ∃ group : PublishedCopyGroup l X publication,
      publication.1 = copy.1 ∧ X.AsyncArrive publication (readyObject l writer.1 1) true ∧
      LoaderReady.generation l X publication 1 = 0 ∧ (copy.2, s) ∈ group.copies := by
  obtain ⟨outputWait, hOutput, hBefore⟩ := hStage.secondAcquire hp hX
  obtain ⟨final, commit, scope, hFinal, hCta, _⟩ :=
    Thread.secondOutputAcquireReads hp hX hOutput
  have hWarp := hFinal.issuerWarp hp hX
  obtain ⟨_, _, wait, hReady, _, hOrdinal⟩ :=
    Thread.initialValueMatchedReplyWithAcquire hp hX hFinal
  have hUse : MmaReady.uses (Thread.Mma.atPrefix l X final.1 wait) = 1 :=
    (Thread.Mma.readyUsesAtPrefix hp hX (PTX.Proof.event_thread_lt hX hFinal.decoded)
      hWarp wait).symm.trans hOrdinal
  have hCursor := (MmaReady.followsOperands hp hX hWarp).cursor wait
  rw [hUse] at hCursor
  have hZero : (Thread.Mma.atPrefix l X final.1 wait).kvAcquires 1 = 0 := hCursor 1
  obtain ⟨completed⟩ := LoaderReady.completedForObservedIssuer hp hX hWarp
    (fun h hc => hFinal.sameReleaseIssuer hp hX h hc) hReady
    (LoaderReady.actualEmptyGuardLower hp hX final.1 1)
  rw [hZero] at completed
  obtain ⟨lane, hProducer⟩ := hCopy.producerLane hp hX
  have hOwner := hCta.2.2
  rw [hBefore.1] at hOwner
  obtain ⟨publication, hLane, hPub, _, hRank, _⟩ :=
    completed.actualPublicationOfLane hp hX lane
  have hThread : publication.1 = copy.1 := by
    rw [hLane, hOwner, ← hSame, ← hProducer]
  have hPublish : X.AsyncArrive publication (readyObject l writer.1 1) true := by
    simpa only [readyObject, Prod.fst, hOwner] using hPub
  obtain ⟨group⟩ := Thread.Loader.publishedCopyGroup hp hX hPublish
  exact ⟨publication, group, hThread, hPublish, hRank,
    hCopy.memberOfInitialPublication hp hX hThread.symm group hPublish hRank⟩

/-- An issued priming V copy precedes an overlapping second-stage staging write. -/
theorem primingValueCopyBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy writer : EvId} {pair : Fin 16} {upper : Bool} {s : Spec} {a : Acc} {data : List Byte}
    {loc : Loc} (hCopy : PrimingValueVector X copy pair upper s)
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hSame : copy.1 / l.block = writer.1 / l.block)
    (hAtCopy : s.dst.Covers loc) (hAtStore : a.Covers loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  obtain ⟨publication, group, hThread, hPub, hRank, hMember⟩ :=
    primingValuePublicationOfSecondStaging hp hX hCopy hStage hSame
  have hPrior := initialValuePublicationBeforeSecondStaging hp hX group hPub hRank hMember
    hAtCopy hStage hAtStore
  have hId : (publication.1, copy.2) = copy := Prod.ext hThread rfl
  rwa [hId] at hPrior

/-- An issued priming V copy precedes every overlapping pending O source read. -/
theorem primingValueCopyBeforeOutputRead {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy issue : EvId} {pair : Fin 16} {upper : Bool} {s : Spec}
    {address x y k : Nat} {spec : TensorStore.Spec} {loc : Loc}
    (hCopy : PrimingValueVector X copy pair upper s) (hAtCopy : s.dst.Covers loc)
    (hIssue : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.async issue (.read (.store x y k))) := by
  apply cacheBeforePendingOutputAfterStaging hp hX hCopy.copy hAtCopy hIssue hRead
  intro writer access data hStage hOther hSame
  exact primingValueCopyBeforeSecondStaging hp hX hCopy hStage hSame hAtCopy hOther

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
