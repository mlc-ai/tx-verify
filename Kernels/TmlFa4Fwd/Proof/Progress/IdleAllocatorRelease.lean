-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.IdleAllocationRendezvous
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) (hCuQ : DrainCuQProtected p X)
include hp hMax hg hw hCuQ

/-- With no assigned tile, each lane of the allocator warp issues the
deallocation of the actual column-zero tile in a maximal execution. -/
theorem idleMmaIssuesDeallocationOfAllGroups (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .tc (.resource .one none (.dealloc 0 512)) := by
  obtain ⟨j,_,_,he,_,_,_,_,_,_⟩ :=
    Mma.idleMmaDeallocationPrefix hp hMax hg hw hCuQ hIdle (fun h => by
      obtain ⟨Y,hY,hTr,_,hReady⟩ := idleAllocationCanReleaseOfAllGroups hp hMax hg hCuQ hIdle h
      exact ⟨Y,hY,hTr,hReady⟩)
  exact ⟨j,_,he,rfl⟩

/-- Each Tensor Memory allocator lane of an idle CTA reaches its actual exit. -/
theorem idleAllocatorExitsOfAllGroups (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  apply Mma.idleMmaExits hp hMax hg hw hCuQ hIdle
  intro lane hLane _ hCta hLast
  obtain ⟨Y,hY,hTr,_,hReady⟩ :=
    idleAllocationCanReleaseOfAllGroups hp hMax hLane hCuQ (hCta.symm ▸ hIdle) hLast
  exact ⟨Y,hY,hTr,hReady⟩

end PTX.Kernels.TmlFa4Fwd.Progress
