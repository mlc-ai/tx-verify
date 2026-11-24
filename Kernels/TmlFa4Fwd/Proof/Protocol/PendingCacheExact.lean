-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheRelease
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (EmptyAcquire recurringUseBefore recurringVectorEvent)
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)
open Loader (kvUseStage kvEmptyPhase)

private theorem pendingCacheReleaseBeforeOwnGeneration {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hVector : recurringVectorEvent e) {spec : Spec} (hKind : e.kind = .copy spec)
    {wait : EvId} {issuer position : Nat}
    (release : EmptyReleaseAt l X (emptyObject l wait.1
      (kvUseStage (recurringUseBefore X (g,index)))) issuer position)
    (hGuard : Resumes kernel X wait (g,index))
    (hSeen : MbarObserved X release.record.id (.thread wait)) :
    release.ordinal < recurringUseBefore X (g,index) / 3 := by
  by_contra! hLater
  let use := recurringUseBefore X (g,index)
  let slot := kvUseStage use
  change use/3 ≤ release.ordinal at hLater
  have hReady := release.matched.ready
  rw [release.matchedSlot] at hReady
  obtain ⟨completion⟩ := actualCompletedForIssuer hp hX release.issue hReady
  have hOrdinal : (Thread.Mma.atPrefix l X issuer release.matched.wait).kvAcquires slot =
      release.ordinal := by unfold Thread.Mma.EmptyReleaseAt.ordinal; rw [release.matchedSlot]
  rw [hOrdinal] at completion
  have hCopy : X.Copy (g,index) spec := Thread.Loader.actualCopyOfRecurringVector he hVector hKind
  obtain ⟨lane,hLane⟩ := Thread.Loader.copyProducer hp hX hCopy
  have hOwner : g/l.block = issuer/l.block := by
    have hCta := release.issuerCta hp hX
    rwa [hGuard.1.1] at hCta
  have hObject := (completion.acquire.record hp hX).1
  obtain ⟨k,entry,publication,hk,hAt,_,hUnit,_,hId,hProducer,hPub,hGen⟩ :=
    Thread.Loader.readyCoverageByOrdinal hp hX hObject completion.record completion.success
      completion.observed
      (fun q _ => (phaseAlignment hp hX (actualEmptyGuardLower hp hX issuer slot) q).1)
      (use/3) hLater lane
  have hSame : publication.1 = g := by
    rw [hProducer, ← hOwner]
    exact hLane.symm
  obtain ⟨producer,j⟩ := publication
  change producer = g at hSame
  subst producer
  have hUse : use = 3 * ((Thread.Loader.atPrefix l X g j).published.countP
      (fun q => q.slot == slot)) + slot.val := by
    rw [hGen]
    change use = 3 * (use/3) + use%3
    omega
  have hEarlier := Thread.Loader.copyBeforeReadyPublicationOfOccurrence hp hX hCopy hPub
    rfl hUse.le
  have hTracked : TracksCpAsync X (g,index) (g,j) :=
    ⟨rfl,hEarlier.2.1,⟨spec,hCopy,(actualCopyShape hX hCopy).completion⟩,_,_,hPub⟩
  obtain ⟨_,_,actual,hActual,_,hDone⟩ := hObject.arrive_source hAt hUnit
  obtain rfl : actual = (g,j) := (Ref.async.inj (hActual.symm.trans hId)).1
  have hDependency :
      EmptyReuseWitness X (.async (issuer,release.index) (.tcNotify release.rank)) (g,j) :=
    ⟨wait,(g,index),release.notification ▸ hSeen,hGuard,hTracked⟩
  have hPath := hDependency.afterIssuerReady hX release.issue release.matched
    release.matched.ready (Nat.le_refl _) hDone
  have hOrder : Before (X.objects (Thread.Loader.readyObject l issuer slot))
      (.async (g,j) .arriveOn) (.thread (issuer,release.matched.wait)) :=
    ⟨k,completion.position,entry,completion.poll,hAt,hId,completion.record,completion.id,hk⟩
  exact Round.Slot.not_before_of_reach hX hPath hOrder

/-- Any actual positive-generation recurring vector has a successful same-slot
guard that observes exactly the preceding release, including in an open packet. -/
theorem pendingCacheGuardObservedReleaseExact {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hVector : recurringVectorEvent e) {spec : Spec} (hKind : e.kind = .copy spec)
    (hPositive : 0 < recurringUseBefore X (g,index) / 3) :
    ∃ (wait : EvId) (issuer position : Nat),
      let use := recurringUseBefore X (g,index)
      let slot := kvUseStage use
      ∃ release : EmptyReleaseAt l X (emptyObject l wait.1 slot) issuer position,
        EmptyAcquire l X wait slot (if kvEmptyPhase use then 1 else 0) ∧
        Resumes kernel X wait (g,index) ∧ release.ordinal = use/3 - 1 ∧
        MbarObserved X release.record.id (.thread wait) := by
  obtain ⟨wait,issuer,position,release,hWait,hResumes,hFloor,hSeen⟩ :=
    pendingCacheGuardObservedRelease hp hX he hVector hPositive
  have hBound := pendingCacheReleaseBeforeOwnGeneration hp hX he hVector hKind release hResumes
    hSeen
  exact ⟨wait,issuer,position,release,hWait,hResumes,by omega,hSeen⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
