-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CommitDestination
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPublicationLifetime
public import Lemmas.Kernel.ExitChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.MBarrier
open Thread (CacheRelease)
open Thread.Mma (atPrefix)
open Thread.Mma.Observation (emptyObject)
open Thread.Loader (readyObject)

private theorem cacheReleaseOfCompletedPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index owner j observed : Nat} {slot : Fin 3} {spec : TcCommit.Spec} {rank : Fin 16}
    {form : Thread.Mma.ReleaseForm}
    (hIssue : Thread.Mma.ReleaseIssue X g index form spec)
    (hTarget : TcCommit.target spec rank = some (emptyObject l owner slot))
    (hOwner : owner / l.block = g / l.block)
    (matched : Thread.Mma.ReleaseMatch l X g index form (emptyObject l owner slot))
    (hSlot : matched.slot = slot)
    {poll : Record Ref} (hPoll : (X.objects (emptyObject l owner slot))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hObserved : observedAt (X.objects (emptyObject l owner slot)) j = some observed)
    (hPhase : (atPrefix l X g matched.wait).kvAcquires slot ≤ observed) :
    rank ∈ X.tcNotified (g,index) ∧
      MBarrier.Before (X.objects (emptyObject l owner slot)) (.async (g,index) (.tcNotify rank))
        poll.id := by
  let loc := emptyObject l owner slot
  let log := X.objects loc
  let phase := (atPrefix l X g matched.wait).kvAcquires slot
  obtain ⟨k, r, hr, hUnit, hClean, hAt⟩ :=
    Thread.Mma.emptyUnitThroughObservedPhase hp hX hPoll hSuccess hObserved hPhase
  obtain ⟨issuer, ⟨release⟩⟩ := Thread.Mma.emptyReleaseAt hp hX hr hUnit
  have hRecord : release.record = r := Option.some.inj (release.atIndex.symm.trans hr)
  have hExact := (phaseAlignment hp hX (actualEmptyGuardLower hp hX owner slot) phase).2
    k issuer release (hRecord ▸ hClean) hAt
  have hIssuer := hIssue.sameIssuer hp hX release.issue
    (hOwner.symm.trans (release.issuerCta hp hX))
  subst issuer
  obtain ⟨a, ha, hKind⟩ := matched.ready
  obtain ⟨b, hb, hKind'⟩ := release.matched.ready
  rw [hSlot] at hKind
  rw [release.matchedSlot] at hKind'
  obtain ⟨_, kind⟩ := a
  obtain ⟨_, kind'⟩ := b
  change kind = _ at hKind
  change kind' = _ at hKind'
  subst kind kind'
  have hOrdinal : (atPrefix l X g release.matched.wait).kvAcquires slot = phase := by
    simpa only [Thread.Mma.EmptyReleaseAt.ordinal, release.matchedSlot] using hExact
  have hCounts := hOrdinal.symm
  simp only [phase, atPrefix, Thread.Mma.kvAcquireCount] at hCounts
  have hWait := MbarRing.Poll.okPoll_index_unique ha hb hCounts
  have hIssueEq := matched.issue_eq_of_wait_eq hp hX hIssue release.issue release.matched hWait
  have hSpec : release.spec = spec := by
    have hActual : X.Commit (g,release.index) release.spec := ⟨_, release.issue⟩
    rw [← hIssueEq] at hActual
    obtain ⟨_, he⟩ := hActual
    have hKnown : X.Commit (g,index) spec := ⟨_, hIssue⟩
    obtain ⟨_, hf⟩ := hKnown
    exact TcKind.commit.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj (he.symm.trans hf))).2)
  have hRank := MbarRing.Notify.rank_eq release.target (hSpec ▸ hTarget)
  have hId : r.id = .async (g,index) (.tcNotify rank) := by
    rw [← hRecord, release.notification, ← hIssueEq, hRank]
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hId] at hPresent
  have hChecked := X.objects_checked hX loc
  obtain ⟨st, hs, hLower⟩ := hChecked.observed_phase hPoll hSuccess hObserved
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hOrder : k < j := by
    by_contra hBad
    obtain ⟨u, hu, hMono⟩ := hChecked.phase_mono hNo (Nat.le_of_not_lt hBad)
      (List.getElem?_eq_some_iff.mp hr).1.le hs
    have hU : u.phase = phase := by
      change (stateBefore log k).map (·.phase) = some phase at hAt
      rwa [hu, Option.map_some, Option.some.injEq] at hAt
    change phase ≤ observed at hPhase
    omega
  exact ⟨hPresent, k, j, r, poll, hr, hId, hPoll, rfl, hOrder⟩

/-- Every cache release is delivered before an exit in its issuing CTA. Its matched
ready acquisition has a loader publication in the same generation, which the final
empty acquire on that lane covers. -/
theorem cacheReleaseFinishedAtExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {spec : TcCommit.Spec} {rank : Fin 16} {slot : Fin 3}
    (hRelease : CacheRelease l X i slot spec rank) (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / l.block) := by
  obtain ⟨g,index⟩ := i
  let lane : Fin 64 := 0
  let loader := Thread.Loader.producer l (g / l.block) lane
  have hCta : loader / l.block = g / l.block := by
    change (g / l.block * l.block + 448 + 0) / l.block = g / l.block
    rw [hp.block]
    omega
  have hEmpty : emptyObject l g slot = emptyObject l loader slot := by
    unfold emptyObject
    rw [hCta]
  have hTarget := hRelease.2.trans (congrArg some hEmpty)
  obtain ⟨form, hForm⟩ := Thread.Mma.releaseOfEmptyTarget hp hX hRelease.1 hTarget
  obtain ⟨matched⟩ := hForm.matchReady hp hX hTarget
  have hSlot : matched.slot = slot := (Thread.Loader.emptyObjectSlotEq matched.target_eq).symm
  have hReady := matched.ready
  rw [hSlot] at hReady
  obtain ⟨completed⟩ := actualCompletedForIssuer hp hX hForm hReady
  obtain ⟨⟨producer,j⟩, hLane, hPub, _, hGeneration, _⟩ :=
    completed.actualPublicationOfLane hp hX lane
  change producer = loader at hLane
  subst producer
  have hSame : readyObject l g slot = readyObject l loader slot := by
    unfold readyObject
    rw [hCta]
  rw [hSame] at hPub
  obtain ⟨site, he⟩ := hPub
  obtain ⟨returnSite, hLast⟩ := hExit loader (PTX.Proof.event_thread_lt hX he) hCta
  rw [List.getLast?_eq_getElem?] at hLast
  have hExited : Thread.Exited X loader := ⟨_, _, hLast, rfl⟩
  obtain ⟨wait,finish,k,phase,poll,hAt,hId,hOk,hSeen,hCoverage,hResume,hOwner⟩ :=
    Thread.Loader.publicationObservedThroughDrain hp hX (i := j) ⟨site,he⟩ hExited
  have hPhase : generation l X (loader,j) slot ≤ phase := hCoverage
  obtain ⟨hPresent, hBefore⟩ := cacheReleaseOfCompletedPhase hp hX hForm hTarget hCta matched
    hSlot hAt hOk hSeen (hGeneration ▸ hPhase)
  rw [hId] at hBefore
  exact SharedFinished.of_completedBefore hPresent (hCta ▸ hOwner)
    (CompletedBefore.of_before hBefore (.single (DepStep.of_resumes l hResume)))

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
