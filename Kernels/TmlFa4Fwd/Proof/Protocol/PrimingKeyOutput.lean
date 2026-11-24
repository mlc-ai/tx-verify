-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInitialKeyGroup
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCacheOverlap
import Kernels.TmlFa4Fwd.Proof.Protocol.TensorInputReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy
open Thread.Loader (PrimingKeyVector PublishedCopyGroup readyObject)

noncomputable section

/-- A second-stage correction write forces the ordinal-zero publication
containing an actual priming K vector in its CTA. -/
theorem primingKeyPublicationOfSecondStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy writer : EvId} {pair : Fin 16} {upper : Bool} {s : Spec} {a : Acc} {data : List Byte}
    (hCopy : PrimingKeyVector X copy pair upper s)
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hSame : copy.1/l.block = writer.1/l.block) :
    ∃ publication, ∃ group : PublishedCopyGroup l X publication,
      publication.1 = copy.1 ∧
      X.AsyncArrive publication (readyObject l writer.1 0) true ∧
      LoaderReady.generation l X publication 0 = 0 ∧ (copy.2,s) ∈ group.copies := by
  obtain ⟨wait,hWait,hLater⟩ := Thread.StageStagingWrite.secondAcquire hp hX hStage
  obtain ⟨commit,spec,scope,hCommit,hCta,_⟩ := Thread.secondOutputAcquireReads hp hX hWait
  obtain ⟨_, hFrags⟩ :=
    Thread.initialKeyIssuesWithDescriptorBeforeSecondOutputCommit hp hX hCommit 0
  obtain ⟨ready,_,_,_,_,_,_,_,hReady,_,hFirst,_⟩ := hFrags 0
  obtain ⟨completion⟩ := LoaderReady.completedForObservedIssuer hp hX (hCommit.issuerWarp hp hX)
    (fun h hc => hCommit.sameReleaseIssuer hp hX h hc) hReady
    (LoaderReady.actualEmptyGuardLower hp hX commit.1 0)
  rw [hFirst] at completion
  obtain ⟨lane,hProducer⟩ := hCopy.producerLane hp hX
  have hOwner := hCta.2.2
  rw [hLater.1] at hOwner
  obtain ⟨publication,hLane,hPub,_,hGeneration,_⟩ := completion.actualPublicationOfLane hp hX lane
  have hThread : publication.1 = copy.1 := by
    rw [hLane,hOwner,← hSame,← hProducer]
  have hPub' : X.AsyncArrive publication (readyObject l writer.1 0) true := by
    simpa only [readyObject,Prod.fst,hOwner] using hPub
  obtain ⟨group⟩ := Thread.Loader.publishedCopyGroup hp hX hPub'
  exact ⟨publication,group,hThread,hPub',hGeneration,
    hCopy.memberOfInitialPublication hp hX hThread.symm group hPub' hGeneration⟩

/-- An issued priming K copy precedes each overlapping second-stage staging write. -/
theorem primingKeyCopyBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy writer : EvId} {pair : Fin 16} {upper : Bool} {s : Spec} {a : Acc} {data : List Byte}
    {loc : Loc} (hCopy : PrimingKeyVector X copy pair upper s)
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hSame : copy.1/l.block = writer.1/l.block)
    (hAtCopy : s.dst.Covers loc) (hAtStore : a.Covers loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  obtain ⟨publication,group,hThread,hPub,hFirst,hMember⟩ :=
    primingKeyPublicationOfSecondStaging hp hX hCopy hStage hSame
  have hPrior := initialKeyPublicationBeforeSecondStaging hp hX group hPub hFirst hMember
    hAtCopy hStage hAtStore
  have hId : (publication.1,copy.2) = copy := Prod.ext hThread rfl
  rwa [hId] at hPrior

/-- An issued priming K copy precedes an overlapping pending output source read. -/
theorem primingKeyCopyBeforeOutputRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy issue : EvId} {pair : Fin 16} {upper : Bool} {s : Spec}
    {address x y k : Nat} {spec : TensorStore.Spec} {loc : Loc}
    (hCopy : PrimingKeyVector X copy pair upper s) (hAtCopy : s.dst.Covers loc)
    (hIssue : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.async issue (.read (.store x y k))) := by
  obtain ⟨stage,writer,a,data,hStage,hCover,hOwner,hBounds,_,_,hPublished⟩ :=
    Thread.Output.actualPublishedStagingSource hp hX hIssue hRead
  obtain ⟨_,hCta,slot,pair',upper',hDst⟩ := cacheOverlap hp hX hIssue hRead hCopy.copy hAtCopy
  have hRange := kvCopyAddress_range (stage := slot.val)
    (lane := copy.1 % l.block) (group := pair') (upper := upper')
    (byte := 0) hp.shared.1 (by have := slot.isLt; omega) pair'.isLt (by decide)
  have hLo := hAtCopy.2.2.1
  rw [hDst] at hLo
  have hStageOne : stage = 1 := hBounds.resolve_left (by
    dsimp only at hLo
    omega)
  subst stage
  have hPrior := primingKeyCopyBeforeSecondStaging hp hX hCopy hStage
    (hCta.trans hOwner.symm) hAtCopy hCover
  obtain ⟨_,hCopyGet⟩ := hCopy.copy
  obtain ⟨_,hIssueGet⟩ := hIssue
  have hSame : SameCta l copy.1 issue.1 :=
    ⟨PTX.Proof.event_thread_lt hX hCopyGet,PTX.Proof.event_thread_lt hX hIssueGet,hCta⟩
  exact .direct (asyncSourceBeforePublishedRead hX hSame hPrior hPublished)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
