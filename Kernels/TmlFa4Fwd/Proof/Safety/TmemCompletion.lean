-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemDelayedLoadCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemMmaCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Safety.TmemAllocated
import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

theorem mmaHasScheduledTile {i : EvId} {dst : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hIssue : X.MmaIssue i dst op accum mask) :
    i.1 / l.block < tilePrefix p p.batch * p.heads := by
  obtain ⟨wait, event, he, hk, hBefore⟩ := Thread.Mma.mmaIssueInitialQueryAcquire hp hX hIssue
  obtain ⟨hWait, phase, _, hPhase⟩ := Protocol.queryAcquirePhaseOfZero hp hX ⟨event, he, hk⟩
  obtain ⟨_, publisher, _, _, hPublished, _, _⟩ := hWait.hasTransactionPair hp hX hPhase
  obtain ⟨hCta, ⟨_, _, hBox⟩, _, _⟩ := hPublished
  have hActive := hBox.active hp hX hCuQ
  rwa [← hBefore.1, ← hCta]

/-- Pending access completion is ruled out for each operation of the deallocating CTA,
using the preserved scheduling offsets to identify the correction lane's work. -/
theorem tensorOperationsCompletedBeforeRelease {i d : EvId} (hCta : i.1 / l.block = d.1 / l.block)
    (hRelease : Deallocation X d) :
    TcMma.CompletedBefore l X i d := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _, _, hLoad⟩
    exact tensorLoadCompletedBeforeRelease hp hX hCta hLoad hRelease
  · rintro ⟨_, _, _, hStore⟩
    exact tensorStoreCompletedBeforeRelease hp hX hCta hStore hRelease
  · rintro (⟨_, _, _, _, hMma⟩ | ⟨_, hCopy⟩ | ⟨_, hShift⟩)
    · exact mmaCompletedBeforeReleaseOfWork hp hX hMma
        (mmaHasScheduledTile hp hX hCuQ hMma) hCta hRelease
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim

/-- An actual MMA uses an allocated cell and completes before each release covering that cell. -/
theorem mmaAccessLifetime {i : EvId} {cell : TcMma.Cell} (hAccess : X.MmaAccess i cell) :
    (∃ cta r, r ∈ X.tmemHistory cta ∧ Tmem.Pair.Covers l X r cell.cta i cell.column) ∧
      ∀ cta r, r ∈ X.tmemHistory cta → Tmem.Pair.Covers l X r cell.cta i cell.column →
        ∀ d, Tmem.Pair.ReleaseOf l X r d → TcMma.CompletedBefore l X i d := by
  obtain ⟨allocated,hMember,hCovers⟩ := mmaAccessAllocated hp hX hAccess
  have owner {r : Tmem.Pair.Requests}
      (hCoverage : Tmem.Pair.Covers l X r cell.cta i cell.column) : cell.cta = r.own.cta := by
    obtain ⟨_, _, _, hOwner, _, _, _⟩ := hCoverage
    exact hOwner
  have hOwner : cell.cta = i.1 / l.block :=
    (owner hCovers).trans ((hX.tmemPair.1 _).2.1 allocated hMember)
  refine ⟨⟨_,allocated,hMember,hCovers⟩,?_⟩
  intro cta r hr hCover d hRelease
  obtain ⟨hScope,hDealloc⟩ := allocationReleaseInOwnerCta hX hr hRelease
  have hUse : i.1 / l.block = d.1 / l.block := by
    rw [hScope, ← owner hCover]
    exact hOwner.symm
  exact tensorOperationsCompletedBeforeRelease hp hX hCuQ hUse hDealloc

end PTX.Kernels.TmlFa4Fwd.Safety
