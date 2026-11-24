-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderMmaHandoff
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorParity
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open Thread.Loader (PublishedCopyGroup publishedCopyGroup readyObject)
open Thread.Mma (ReadyPoll ReleaseForm ReleaseIssue atPrefix)
open Thread.Mma.Observation (emptyObject)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The actual loader trace supplies each later publication's empty observation bound. -/
theorem actualEmptyGuardLower (owner : Nat) (slot : Fin 3) : EmptyGuardLower l X owner slot :=
  EmptyGuardLower.ofAlternation hp hX fun _ hPub hPos =>
    Thread.Loader.actualPositivePublicationEmptyAlternation hp hX hPub hPos

/-- An actual MMA ready acquire on the release issuer's lane observes its own
role-machine generation. -/
theorem actualCompletedForIssuer {g wait index parity : Nat} {slot : Fin 3} {form : ReleaseForm}
    {spec : TcCommit.Spec} (anchor : ReleaseIssue X g index form spec)
    (hReady : ReadyPoll l X g wait slot parity true .cta) :
    Nonempty (Completed l X (g, wait) slot ((atPrefix l X g wait).kvAcquires slot)) :=
  completedForIssuer hp hX anchor hReady (actualEmptyGuardLower hp hX g slot)

/-- The actual ready acquire sees the exact-generation publication of each loader lane,
including its completed arrive-on and its visible copy writes. -/
theorem Completed.actualPublicationOfLane {wait : EvId} {slot : Fin 3} {phase : Nat}
    (h : Completed l X wait slot phase) (lane : Fin 64) :
    ∃ issue, issue.1 = Thread.Loader.producer l (wait.1 / l.block) lane ∧
      X.AsyncArrive issue (readyObject l wait.1 slot) true ∧
      X.async.arrived issue = true ∧ generation l X issue slot = phase ∧
      ∀ copy, TracksCpAsync X copy issue → AsyncFinished l X copy (.write .copy) wait :=
  h.visiblePublicationOfLane hp hX (actualEmptyGuardLower hp hX wait.1 slot) lane

/-- The known generation selects both the actual producer lane and its ordinary-copy
group. Every concrete vector of that group covering the requested operand byte
has a visible write ordered before the MMA's read. -/
theorem Completed.actualCopyGroupBeforeOperand {wait mma : EvId} {slot : Fin 3}
    {phase d index : Nat} {isB accum : Bool} {mask : List Nat} {op : TcMma.OperandSpec} {loc : Loc}
    (h : Completed l X wait slot phase) (lane : Fin 64) (hMma : X.MmaIssue mma d op accum mask)
    (hEarlier : TraceBefore X wait mma)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) :
    ∃ (issue : EvId) (group : PublishedCopyGroup l X issue),
      issue.1 = Thread.Loader.producer l (wait.1 / l.block) lane ∧
      X.AsyncArrive issue (readyObject l wait.1 slot) true ∧ generation l X issue slot = phase ∧
      ∀ j spec, (j, spec) ∈ group.copies → spec.dst.Covers loc →
        (∃ bytes, X.MemWrites (.async (issue.1, j) (.write .copy)) spec.dst bytes) ∧
        modelCausality l X loc (.async (issue.1, j) (.write .copy))
          (.async mma (.mmaRead isB index)) := by
  obtain ⟨issue, hLane, hPub, hPhase, hOrder⟩ :=
    h.publicationBeforeOperand hp hX (actualEmptyGuardLower hp hX wait.1 slot)
      lane hMma hEarlier hLoc
  obtain ⟨group⟩ := publishedCopyGroup hp hX hPub
  refine ⟨issue, group, hLane, hPub, hPhase, ?_⟩
  intro j spec hj hCover
  obtain ⟨_, hj, hCopy⟩ := (group.member j spec).mp hj
  have hBefore : j < issue.2 := by have := group.closesAt; omega
  exact hOrder (issue.1, j) spec
    ⟨rfl, hBefore, ⟨spec, hCopy, (actualCopyShape hX hCopy).completion⟩, _, _, hPub⟩ hCopy hCover

/-- The guard of an actual later publication sees exactly the release of the
preceding generation, even when this publication has not yet arrived. -/
theorem actualReleaseForNextPublicationExact {owner n : Nat} {slot : Fin 3} {publication : EvId}
    (hPub : X.AsyncArrive publication (readyObject l owner slot) true)
    (hGeneration : generation l X publication slot = n + 1) :
    ∃ (guard : Thread.Loader.OrderedGuardedReuse l X publication slot) (g k : Nat)
      (release : Thread.Mma.EmptyReleaseAt l X (emptyObject l guard.acquire.1 slot) g k),
      release.ordinal = n ∧ MbarObserved X release.record.id (.thread guard.acquire) := by
  obtain ⟨guard, j, phase, poll, hPoll, hId, hSuccess, hObserved, hFloor⟩ :=
    actualEmptyGuardLower hp hX owner slot publication n hPub hGeneration
  have hLoc : emptyObject l owner slot = emptyObject l guard.acquire.1 slot := by
    simp only [emptyObject, guard.issuer, publicationCta hp hX hPub]
  rw [hLoc] at hPoll hObserved
  obtain ⟨k, r, hAt, hAction, hClean, hPhase⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hPoll hSuccess hObserved (Nat.le_refl _)
  obtain ⟨g, ⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hAt hAction
  have hSame := Option.some.inj (hAt.symm.trans release.atIndex)
  have hExact := (phaseAlignment hp hX (actualEmptyGuardLower hp hX guard.acquire.1 slot)
    phase).2 k g release (hSame ▸ hClean) hPhase
  have hNoInval := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (emptyObject l guard.acquire.1 slot)
  have hObs := hX.observed_of_phase hNoInval hAt hClean
    (by rw [hAction]; trivial) hPoll hSuccess hPhase hObserved
  rw [hSame, hId] at hObs
  have hPhaseEq : phase = n := by
    refine Nat.le_antisymm ?_ hFloor
    by_contra! hLater
    have hReady := release.matched.ready
    rw [release.matchedSlot] at hReady
    obtain ⟨completion⟩ := actualCompletedForIssuer hp hX release.issue hReady
    unfold Thread.Mma.EmptyReleaseAt.ordinal at hExact
    rw [release.matchedSlot] at hExact
    rw [hExact] at completion
    have hCta : owner / l.block = g / l.block := by
      rw [publicationCta hp hX hPub, ← guard.issuer, release.issuerCta hp hX]
    have hObject : readyObject l owner slot = readyObject l g slot :=
      congrArg (fun cta => Prologue.initObject l cta (Loader.readySlot slot)) hCta
    rw [hObject] at hPub
    obtain ⟨lane, hLane⟩ := Thread.Loader.publicationProducer hp hX hPub
    let o := (completion.acquire.record hp hX).1
    obtain ⟨i, entry, issue, hi, hEntry, _, hUnit, _, hEntryId, hIssuer, hActual, hRank⟩ :=
      Thread.Loader.readyCoverageByOrdinal hp hX o completion.record completion.success
        completion.observed
        (fun q _ => (phaseAlignment hp hX (actualEmptyGuardLower hp hX g slot) q).1)
        (n + 1) hLater lane
    have hSame := Thread.Loader.publicationUniqueAtSlot hp hX hActual hPub
      (hIssuer.trans hLane.symm) (hRank.trans hGeneration.symm)
    subst issue
    obtain ⟨_, _, actual, hActualId, _, hDone⟩ := o.arrive_source hEntry hUnit
    have hEq : actual = publication := (Ref.async.inj (hActualId.symm.trans hEntryId)).1
    subst actual
    have hWitness : EmptyReuseWitness X (.async (g, release.index) (.tcNotify release.rank))
        publication :=
      ⟨guard.acquire, guard.copy, release.notification ▸ hObs, guard.guarded, guard.tracked⟩
    have hPath := hWitness.afterIssuerReady hX release.issue release.matched release.matched.ready
      (Nat.le_refl _) hDone
    have hOrder : MBarrier.Before (X.objects (readyObject l g slot))
        (.async publication .arriveOn) (.thread (g, release.matched.wait)) :=
      ⟨i, completion.position, entry, completion.poll, hEntry, hEntryId,
        completion.record, completion.id, hi⟩
    exact Round.Slot.not_before_of_reach hX hPath hOrder
  exact ⟨guard, g, k, release, hExact.trans hPhaseEq, hObs⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
