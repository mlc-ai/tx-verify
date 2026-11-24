-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainCoverage
public import Lemmas.Kernel.ExitChain
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Loader

private theorem observedPublicationFinished {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {issue wait : EvId}
    (hOwner : wait.1 / l.block = cta) (hExit : CtaExited l X cta)
    (hSeen : MbarObserved X (.async issue .arriveOn) (.thread wait)) :
    SharedFinished l kernel Assumptions.all X (.async issue .arriveOn) cta := by
  obtain ⟨hPresent, w, loc, acquire, scope, hEq, hWait, _⟩ := hSeen
  obtain rfl := Ref.thread.inj hEq
  obtain ⟨site, parity, he⟩ := hWait.1
  have hg := PTX.Proof.event_thread_lt hX he
  obtain ⟨returnSite, hLast⟩ := hExit wait.1 hg hOwner
  let finish := (X.tr wait.1).length - 1
  have hReturn : X.get (wait.1, finish) = some ⟨returnSite, .exit⟩ := by
    change (X.tr wait.1)[finish]? = _
    rwa [← List.getLast?_eq_getElem?]
  have hLen : wait.2 < (X.tr wait.1).length := (List.getElem?_eq_some_iff.mp he).1
  have hLt : wait.2 < finish := by
    by_contra! h
    have hSame : wait.2 = finish := by dsimp [finish] at *; omega
    rw [show wait = (wait.1, finish) from Prod.ext rfl hSame, hReturn] at he
    cases he
  have hLater : finish < (X.tr wait.1).length := (List.getElem?_eq_some_iff.mp hReturn).1
  obtain ⟨_, hSpin⟩ := actualCanonicalPoll hX he
  have hResume : Resumes kernel X wait (wait.1, finish) :=
    Resumes.of_spin he hSpin rfl hLt hLater
  exact SharedFinished.of_completedBefore (finish := (wait.1, finish)) hPresent
    ⟨hg, hOwner, _, hReturn⟩
    (CompletedBefore.of_before hWait.before (.single (DepStep.of_resumes l hResume)))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A completed ready acquisition observes each publication of its own generation. -/
theorem Completed.observesPublication {wait issue : EvId} {slot : Fin 3} {phase : Nat}
    (h : Completed l X wait slot phase)
    (hPub : X.AsyncArrive issue (readyObject l wait.1 slot) true)
    (hPhase : generation l X issue slot = phase) :
    MbarObserved X (.async issue .arriveOn) (.thread wait) := by
  have o := (h.acquire.record hp hX).1
  obtain ⟨lane, hLane⟩ := publicationProducer hp hX hPub
  have hGuard := actualEmptyGuardLower hp hX wait.1 slot
  obtain ⟨k, r, actual, _, hAt, hClean, hAction, hAtPhase, hId, hProducer, hActual, hPhase'⟩ :=
    readyCoverageByOrdinal hp hX o h.record h.success h.observed
      (fun q _ => (phaseAlignment hp hX hGuard q).1) phase (Nat.le_refl _) lane
  have hEq := publicationUniqueAtSlot hp hX hActual hPub
    (hProducer.trans hLane.symm) (hPhase'.trans hPhase.symm)
  subst actual
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX)
    (readyObject l wait.1 slot)
  have hSeen := hX.observed_of_phase hNo hAt hClean (hAction.symm ▸ trivial)
    h.record h.success hAtPhase h.observed
  simpa only [hId, h.id] using hSeen

/-- A publication completed by a ready acquire precedes the observing CTA's exit. -/
theorem Completed.publicationFinished {wait issue : EvId} {slot : Fin 3} {phase : Nat}
    (h : Completed l X wait slot phase)
    (hPub : X.AsyncArrive issue (readyObject l wait.1 slot) true)
    (hPhase : generation l X issue slot = phase) (hExit : CtaExited l X (wait.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async issue .arriveOn) (wait.1 / l.block) :=
  observedPublicationFinished hX rfl hExit (h.observesPublication hp hX hPub hPhase)

/-- An empty acquire past a publication's generation establishes a matching ready
observer in the same CTA, even when the acquire sees a later release. -/
theorem publicationFinishedOfEmptyPhase {issue : EvId} {owner position observed : Nat}
    {slot : Fin 3} {poll : Record Ref} (hPub : X.AsyncArrive issue (readyObject l owner slot) true)
    (hPoll : (X.objects (Thread.Mma.Observation.emptyObject l owner slot))[position]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hSeen : observedAt (X.objects (Thread.Mma.Observation.emptyObject l owner slot)) position =
      some observed) (hThrough : generation l X issue slot ≤ observed)
    (hExit : CtaExited l X (owner / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async issue .arriveOn) (owner / l.block) := by
  obtain ⟨k, r, hAt, hUnit, hClean, hPhase⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hPoll hSuccess hSeen hThrough
  obtain ⟨g, ⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hAt hUnit
  have hEq : release.record = r := Option.some.inj (release.atIndex.symm.trans hAt)
  have hOrdinal := (phaseAlignment hp hX (actualEmptyGuardLower hp hX owner slot)
    (generation l X issue slot)).2 k g release (by simpa only [hEq] using hClean) hPhase
  have hSlot := release.matchedSlot
  have hReady := release.matched.ready
  rw [hSlot] at hReady
  obtain ⟨ready⟩ := actualCompletedForIssuer hp hX release.issue hReady
  have hOwner := release.issuerCta hp hX
  have hTarget : readyObject l owner slot = readyObject l g slot :=
    congrArg (fun c => Prologue.initObject l c (Loader.readySlot slot)) hOwner
  rw [hTarget] at hPub
  unfold Thread.Mma.EmptyReleaseAt.ordinal at hOrdinal
  rw [hSlot] at hOrdinal
  exact hOwner.symm ▸ ready.publicationFinished hp hX hPub hOrdinal.symm (hOwner ▸ hExit)

omit hp hX in
/-- A tracked copy write finishes before the same owner exit as its publication. -/
theorem copyFinishedOfPublication {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} {issue copy : EvId}
    (hTrack : TracksCpAsync X copy issue)
    (hDone : SharedFinished l kernel Assumptions.all X (.async issue .arriveOn) cta) :
    SharedFinished l kernel Assumptions.all X (.async copy (.write .copy)) cta := by
  have hArrived : X.async.arrived issue = true := hDone.1
  have hWritten : (X.async.copies copy).writeBytes.isSome := (hX.tma.2.2.2 _ hArrived).2 _ hTrack
  exact SharedFinished.of_stage (j := issue) (q := .arriveOn) hWritten
    (.inr ⟨rfl, rfl, hTrack, hWritten, hArrived⟩) hDone

omit hp hX in
private theorem exitedLane {l : Launch} {X : Execution} {g : Nat} (hg : g < l.threads)
    (hExit : CtaExited l X (g / l.block)) : Thread.Exited X g := by
  obtain ⟨site, hLast⟩ := hExit g hg rfl
  rw [List.getLast?_eq_getElem?] at hLast
  exact ⟨(X.tr g).length-1, _, hLast, rfl⟩

/-- A delivered ready generation in the issuer's CTA includes the publication and
finishes it before the exit. The actual final drain supplies the observer. -/
theorem actualPublicationFinishedAtExit {issue : EvId} {loc : Loc}
    (hPub : X.AsyncArrive issue loc true) (hExit : CtaExited l X (issue.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async issue .arriveOn) (issue.1 / l.block) := by
  obtain ⟨g, i⟩ := issue
  obtain ⟨site, he⟩ := hPub
  obtain ⟨pub, _, hObject, _⟩ := readyObservation hp hX he rfl
  have hg := PTX.Proof.event_thread_lt hX he
  have hActual : X.AsyncArrive (g,i) (readyObject l g pub.slot) true := hObject ▸ ⟨site,he⟩
  obtain ⟨_, _, _, _, _, hAt, _, hSuccess, hSeen, hPhase, _, _⟩ :=
    publicationObservedThroughDrain hp hX hActual (exitedLane hg hExit)
  exact publicationFinishedOfEmptyPhase hp hX hActual hAt hSuccess hSeen hPhase hExit

/-- Every ordinary loader copy in an exited CTA is tracked by a publication whose
ready acquire completes before the CTA's exit. -/
theorem actualCopyFinishedAtExit {copy : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy copy spec)
    (hExit : CtaExited l X (copy.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async copy (.write .copy)) (copy.1 / l.block) := by
  have ⟨site, he⟩ := hCopy
  obtain ⟨issue, _, hSame, hPub, hTrack⟩ :=
    copyPublicationAtExit hX hCopy (exitedLane (PTX.Proof.event_thread_lt hX he) hExit)
  have hCta : issue.1 / l.block = copy.1 / l.block :=
    congrArg (fun g => g / l.block) hSame
  exact copyFinishedOfPublication hX hTrack
    (hCta ▸ actualPublicationFinishedAtExit hp hX hPub (hCta.symm ▸ hExit))

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
