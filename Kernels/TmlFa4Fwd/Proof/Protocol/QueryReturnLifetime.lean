-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryReturnCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryLifetime
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Lemmas.Kernel.CommitNextExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem queryReturnHasWork (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec}
    {rank : Fin 16} (hi : Thread.Mma.QueryReturn l X i stage spec rank) :
    i.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨wait, e, hLane, he, hk⟩ := Thread.Mma.queryReturnInitialAcquire hp hX hi
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e, he, hk⟩
  obtain ⟨_, input, _, _, hInput, _, _⟩ := hAcquire.hasTransactionPair hp hX hPhase
  obtain ⟨hCta, ⟨plane, s, hBox⟩, _, _⟩ := hInput
  rw [← hLane, ← hCta]
  exact hBox.active hp hX hCuQ

/-- Before an active CTA exits the loader observes the second query return notification. -/
theorem secondQueryReturnObservedAtExit (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {cta : Nat} (hGrid : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads) (hExit : CtaExited l X cta) :
    ∃ issue spec rank wait finish, Thread.Mma.QueryReturn l X issue 1 spec rank ∧
      issue.1 / l.block = cta ∧ MbarObserved X (.async issue (.tcNotify rank)) (.thread wait) ∧
      Resumes kernel X wait finish ∧ OwnerExit l X cta finish := by
  obtain ⟨acquire, e, _, hAcqCta, he, hk, _, _⟩ :=
    queryAcquireEnablesExit hp hX hGrid hWork hExit 1
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e, he, hk⟩
  obtain ⟨_, input, _, _, hInput, _, _⟩ := hAcquire.hasTransactionPair hp hX hPhase
  obtain ⟨hInputCta, ⟨plane, s, hBox⟩, _, _⟩ := hInput
  have hInputOwner := hInputCta.trans hAcqCta
  obtain ⟨wait, finish, ⟨event, hWait, hKind⟩, hResumes, hFinish⟩ :=
    Loader.queryReturnWaitBeforeOwnerExit hp hX hBox (hInputOwner.symm ▸ hExit)
  have hWaitCta : wait.1 / l.block = input.1 / l.block := by
    rw [hResumes.1.1]
    exact hFinish.2.1
  have hKind' : event.kind =
      .wait (Loader.secondQueryEmpty l (wait.1 / l.block)) 0 true true .cta := by
    rw [hKind, hWaitCta]
    rfl
  obtain ⟨issue, spec, rank, hIssued, hCta, hTarget, hObs⟩ :=
    Loader.secondQueryEmptyObserver hp hX hWait hKind'
  have hReturn : Thread.Mma.QueryReturn l X issue 1 spec rank :=
    ⟨hIssued, by rw [hCta]; exact hTarget⟩
  exact ⟨issue, spec, rank, wait, finish, hReturn,
    hCta.trans (hWaitCta.trans hInputOwner), hObs, hResumes, hInputOwner ▸ hFinish⟩

/-- Both query return notifications finish at owner exit. The loader observes the second;
the existing selected commit-order rule covers its unobserved predecessor. -/
theorem queryReturnFinishedAtExit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec}
    {rank : Fin 16} (hi : Thread.Mma.QueryReturn l X i stage spec rank)
    (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / l.block) := by
  obtain ⟨_, he⟩ := hi.1
  have hGrid := NamedBar.cta_lt (PTX.Proof.event_thread_lt hX he)
  have hWork := queryReturnHasWork hp hX hCuQ hi
  obtain ⟨issue, found, observed, wait, finish, hSecond, hCta, hObserved, hResume, hFinish⟩ :=
    secondQueryReturnObservedAtExit hp hX hGrid hWork hExit
  have hWitness := Witness.of_mbarObserved (L := l) hObserved
  fin_cases stage
  · obtain ⟨rfl, hNext⟩ :=
      Thread.Mma.queryReturnCommitNext hp hX hi hSecond hCta.symm hObserved.1
    have hBefore : X.RefPresent (.async i (.tcNotify rank)) := hNext.2.2.2.1
    exact SharedFinished.of_commitNext hBefore hNext hWitness
      (.single (DepStep.of_resumes l hResume)) hFinish
  · obtain ⟨rfl, rfl⟩ := Thread.Mma.queryReturnUnique hp hX hi hSecond hCta.symm
    exact SharedFinished.of_observer_exit hObserved.1 hWitness hResume hFinish

end PTX.Kernels.TmlFa4Fwd.Protocol
