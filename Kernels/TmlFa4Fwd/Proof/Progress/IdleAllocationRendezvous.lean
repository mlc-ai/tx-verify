-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.CorrectionIdle
public import Kernels.TmlFa4Fwd.Proof.Progress.SoftmaxIdle
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRendezvous
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Lemmas.Step.CtaBarFinishExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- Every lane using the shared Tensor Memory allocation issues the second rendezvous
when its CTA has no tile. -/
theorem idleAllocationParticipantsArriveOfAllGroups (hw : warpIndex l g < 13)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j mode, FinalAllocationArrival X (g,j) mode := by
  by_cases hSoft : warpIndex l g < 8
  · obtain ⟨j, hj⟩ := idleSoftmaxReachesFinalAllocationForBatches hp hMax hg hSoft hCuQ hIdle
    exact ⟨j,.arrive,hj⟩
  by_cases hCorr : warpIndex l g < 12
  · obtain ⟨j, hj⟩ :=
      idleCorrectionReachesFinalAllocationForBatches hp hMax hg (by omega) hCorr hCuQ hIdle
    exact ⟨j,.arrive,hj⟩
  · obtain ⟨j, _, hj⟩ :=
      Mma.idleMmaReachesTerminalRendezvous hp hMax hg (by omega) hCuQ hIdle
    exact ⟨j+1,.sync,FinalAllocationArrival.of_decoded (by decide) hj⟩

/-- A final allocation wait can return once all participants have actually arrived.
The administrative extension preserves traces and memory writes. -/
theorem finalAllocationCanReleaseOfArrivals (hCuQ : DrainCuQProtected p X)
    (hArrived : ∀ lane < l.threads, warpIndex l lane < 13 → lane/l.block = g/l.block →
      ∃ j mode, FinalAllocationArrival X (lane,j) mode)
    (hLast : FinalAllocationArrival X (g,(X.tr g).length-1) .sync) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Step.Released l Y g := by
  have hOrdinal := finalAllocationArrivalOrdinal hp hMax.1 hLast
  obtain ⟨site, _, he⟩ := hLast.decoded
  refine NamedBar.sync_release_preserving_writes hMax Assumptions.wfStep.ctaHistory ?_
    (allocationBarrierShape hp) (allocationBarrierSources hp hMax.1) hg he ?_
  · intro Y hY _ hWrites
    exact Protocol.noActualNamedBarrierFault hp hY (by
      intro i hi k hk w a bs hWrite
      apply hCuQ i hi k hk w a bs
      simpa only [hWrites] using hWrite)
  · intro y hy hY
    let peer := g/l.block*l.block+y
    have hBlock := NamedBar.block_pos_of_thread_lt hg
    have hThread : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hy
    obtain ⟨hCta,hMod⟩ := NamedBar.lane_cta (c := g/l.block) hBlock hy
    have hWarp : warpIndex l peer < 13 := by
      change peer % l.block / 32 < 13
      rw [hMod]
      exact Finset.mem_range.mp hY
    obtain ⟨j, mode, hPeer⟩ := hArrived peer hThread hWarp hCta
    have hAt := finalAllocationArrivalOrdinal hp hMax.1 hPeer
    obtain ⟨site, _, hGet⟩ := hPeer.decoded
    exact ⟨j,site,mode,hGet,hAt.trans hOrdinal.symm⟩

/-- The final allocation wait of an idle CTA can return after its actual arrivals. -/
theorem idleAllocationCanReleaseOfAllGroups (hCuQ : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block)
    (hLast : FinalAllocationArrival X (g,(X.tr g).length-1) .sync) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Step.Released l Y g :=
  finalAllocationCanReleaseOfArrivals hp hMax hg hCuQ
    (fun _ hLane hWarp hCta => idleAllocationParticipantsArriveOfAllGroups
      hp hMax hLane hWarp hCuQ (hCta ▸ hIdle)) hLast

end PTX.Kernels.TmlFa4Fwd.Progress
