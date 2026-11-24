-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.IdleAllocatorRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.IdleParticipantExit
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleOutputFree

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- All lanes that use the Tensor Memory allocation exit from a CTA without a tile. -/
theorem idleAllocationParticipantsExitOfAllGroups (hw : warpIndex l g < 13)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  by_cases hMma : warpIndex l g = 12
  · exact idleAllocatorExitsOfAllGroups hp hMax hg hMma hCuQ hIdle
  let allocator := g/l.block*l.block+384
  have hWithin : 384 < l.block := by rw [hp.block]; decide
  have hCTA := NamedBar.cta_lt hg
  have ha : allocator < l.threads := NamedBar.cta_thread_lt hCTA hWithin
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hWithin
  have hWarp : warpIndex l allocator = 12 := by
    unfold warpIndex allocator
    rw [hLocal]
  obtain ⟨j,e,he,heKind⟩ := idleMmaIssuesDeallocationOfAllGroups hp hMax ha hWarp
    hCuQ (hCta ▸ hIdle)
  have hDealloc := Deallocation.ofKind he heKind
  by_cases hSoft : warpIndex l g < 8
  · exact idleSoftmaxExitsOfDeallocationForBatches hp hMax hg hSoft hCuQ hIdle
      (fun stage => Protocol.Statistics.idleStatisticsPhaseZero hp hMax hCTA
        stage hIdle)
      hCta.symm hDealloc
  · exact Correction.idleExitForBatchesOfDeallocation hp hMax hg (by omega) (by omega)
      hCuQ hIdle
      (Protocol.Output.idleFreePhaseZeroOfAllGroups hp hMax hCTA 1 hCuQ hIdle)
      hCta.symm hDealloc

end PTX.Kernels.TmlFa4Fwd.Progress
