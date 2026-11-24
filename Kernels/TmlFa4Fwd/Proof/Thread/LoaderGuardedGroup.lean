-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyChronology

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX

/-- An actual empty checkpoint resumes at every later event of the lane. -/
theorem GuardedReuse.resumesOfTraceBefore {l : Launch} {X : Execution}
    {publication event : EvId} {slot : Fin 3} (guard : GuardedReuse l X publication slot)
    (hTrace : TraceBefore X guard.acquire event) :
    Resumes kernel X guard.acquire event := by
  obtain ⟨ev, hWait, hKind⟩ := guard.empty
  refine ⟨hTrace, ?_⟩
  have hResume := guard.guarded.2
  simp only [hWait, Option.map_some, hKind, Kind.resume] at hResume ⊢
  obtain ⟨pc, exit, loc, parity, acq, scope, he, hSpin, _⟩ := hResume
  exact ⟨pc, exit, loc, parity, acq, scope, he, hSpin, hTrace⟩

/-- The observed empty checkpoint guards every vector of the identified ordinary group. -/
theorem OrderedGuardedReuse.resumesCopy {l : Launch} {X : Execution}
    {publication : EvId} {slot : Fin 3} (guard : OrderedGuardedReuse l X publication slot)
    (group : PublishedCopyGroup l X publication) {j : Nat} {spec : AsyncCopy.Spec}
    (hMember : (j, spec) ∈ group.copies) :
    Resumes kernel X guard.acquire (publication.1, j) := by
  obtain ⟨hFirst, _, pc, hCopy⟩ := (group.member j spec).mp hMember
  obtain ⟨ev, hWait, hKind⟩ := guard.empty
  have hBeforeCommit : guard.acquire.2 < group.commit := by
    have hBeforeCopy := guard.guarded.1.2.1
    have hBeforePub := guard.tracked.2.1
    have hCloses := group.closesAt
    omega
  have hBeforeFirst : guard.acquire.2 < group.first := by
    by_contra hNot
    have hGet : X.get (publication.1, guard.acquire.2) = some ev := by
      rw [← guard.issuer]
      exact hWait
    exact group.noWait (by omega) hBeforeCommit hGet hKind
  have hTrace : TraceBefore X guard.acquire (publication.1, j) :=
    ⟨guard.issuer, hBeforeFirst.trans_le hFirst, (List.getElem?_eq_some_iff.mp hCopy).1⟩
  exact guard.toGuardedReuse.resumesOfTraceBefore hTrace

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
