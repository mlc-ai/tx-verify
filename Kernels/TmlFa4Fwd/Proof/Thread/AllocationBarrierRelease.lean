-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Kernels.TmlFa4Fwd.Proof.AllocationBarrierGeneration
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof Prologue

/-- An actual Tensor Memory deallocation attempt. -/
@[no_expose] def Deallocation (X : Execution) (d : EvId) : Prop :=
  ∃ site base columns group dst,
    X.get d = some ⟨site, .tc (.resource group dst (.dealloc base columns))⟩

theorem Deallocation.of_decoded {X : Execution} {d : EvId} {site base columns : Nat}
    {group : CtaGroup} {dst : Option Loc}
    (he : X.get d = some ⟨site, .tc (.resource group dst (.dealloc base columns))⟩) :
    Deallocation X d := ⟨site, base, columns, group, dst, he⟩

/-- Recover the recorded resource instruction from a deallocation observation. -/
theorem Deallocation.decoded {X : Execution} {d : EvId} (h : Deallocation X d) :
    ∃ site base columns group dst,
      X.get d = some ⟨site, .tc (.resource group dst (.dealloc base columns))⟩ := h

/-- The final allocator sync records every participant's terminal arrival and orders
its earlier events before the release. -/
theorem finalAllocationMemberBeforeDeallocation
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {d : EvId} (hg : g < l.threads) (hWarp : warpIndex l g < 13)
    (hCta : g / l.block = d.1 / l.block) (hRelease : Deallocation X d) :
    ∃ j mode, FinalAllocationArrival X (g,j) mode ∧
      ∀ i < j, baseCausality l X (g,i) d := by
  obtain ⟨site, base, columns, group, dst, hd⟩ := hRelease
  have hOwner := event_thread_lt hX hd
  obtain ⟨wait, hBefore, key, _, _, hk, hReleased, hWait⟩ :=
    deallocationFollowsFinalSync hp hX hd
  have hFinal : FinalAllocationArrival X (d.1,wait) .sync :=
    FinalAllocationArrival.of_decoded (by decide) hWait
  have hOrdinal := finalAllocationArrivalOrdinal hp hX hFinal
  let sources := TmlFa4Fwd.Mma.allocationBarrierSources hp hX
  let shape := TmlFa4Fwd.Mma.allocationBarrierShape hp
  have hBound : d.2 < (X.tr d.1).length := PTX.len_of_get hd
  have hPass : wait + 1 < (X.tr d.1).length := by omega
  have hMember : g % l.block / 32 ∈ Finset.range 13 := Finset.mem_range.mpr hWarp
  obtain ⟨arrival, mode, hArrive, hOrdinalEq⟩ := memberBarrierArrival hX sources shape
    hFinal.arrival hPass hCta hMember (by
      rintro ⟨finish, ⟨pc, kind⟩, hExit, rfl⟩
      obtain ⟨j, _, mode, hArrival⟩ := finalAllocationArrivalBeforeExit hp hX hWarp ⟨pc, hExit⟩
      exact ⟨j, mode, hArrival.arrival,
        (finalAllocationArrivalOrdinal hp hX hArrival).trans hOrdinal.symm⟩)
  have hOne := hOrdinalEq.trans hOrdinal
  have hPeer := finalAllocationArrivalOfOrdinal hp hX hArrive hOne
  have hKey : key = 18 := by
    have h := sources.arrival_key hX shape hWait (CtaBarK.arrival hk)
    change key = 2 + 16 * observedBarrierOrdinal X (d.1,wait) 2 at h
    rwa [hOrdinal] at h
  subst key
  have hReleaseAt : CtaBarrier.Released l.block (X.barriers (g/l.block)) 2
      (observedBarrierOrdinal X (g,arrival) 2) := by
    rw [hOne, hCta]
    exact hReleased
  have hPeerKey := barrierArrivalKeyOfReleased hX sources shape hArrive hReleaseAt
  rw [hOne] at hPeerKey
  refine ⟨arrival, mode, hPeer, ?_⟩
  intro i hi
  exact
    .single (.inr (.inl ⟨⟨hg, hOwner, hCta⟩, 18, arrival, wait, hPeerKey, hk,
      hi, hBefore, hBound⟩))


variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {i d : EvId}
    (hCta : i.1 / l.block = d.1 / l.block) (hData : TensorDataEvent X i)
include hp hX hCta hData

/-- Each data operation precedes its lane's actual final arrival and the release. -/
theorem tensorDataFinalArrivalBeforeDeallocation (hRelease : Deallocation X d) :
    (∃ j mode, i.2 < j ∧ FinalAllocationArrival X (i.1,j) mode) ∧ baseCausality l X i d := by
  obtain ⟨g, index⟩ := i
  obtain ⟨e, he, hTensor⟩ := hData
  have hg := event_thread_lt hX he
  obtain ⟨_, _, startup, hs, hEntry⟩ :=
    TmlFa4Fwd.Mma.tensorEventAfterAllocationEntry hp hX he hTensor
  have hWarp : warpIndex l g < 13 := by
    rcases TmlFa4Fwd.Mma.allocationEntryRole hp hX hs hEntry with
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> omega
  obtain ⟨arrival, mode, hPeer, hSync⟩ :=
    finalAllocationMemberBeforeDeallocation hp hX hg hWarp hCta hRelease
  have hBefore := hPeer.afterTensorData hp hX ⟨e, he, hTensor⟩
  exact ⟨⟨arrival, mode, hBefore, hPeer⟩, hSync index hBefore⟩

/-- A data operation in a CTA that has attempted release is followed by another lane event. -/
theorem tensorDataResumedBeforeDeallocation (hRelease : Deallocation X d) :
    i.2 + 1 < (X.tr i.1).length := by
  obtain ⟨j, _, hBefore, hPeer⟩ :=
    (tensorDataFinalArrivalBeforeDeallocation hp hX hCta hData hRelease).1
  obtain ⟨_, _, hArrival⟩ := hPeer.decoded
  have hLength : j < (X.tr i.1).length := PTX.len_of_get hArrival
  omega

/-- The allocator's final synchronization orders every data operation of its CTA before
the deallocation attempt, including a lane's recorded `wait::ld` or `wait::st`. -/
theorem tensorDataBeforeDeallocation (hRelease : Deallocation X d) :
    baseCausality l X i d :=
  (tensorDataFinalArrivalBeforeDeallocation hp hX hCta hData hRelease).2

end PTX.Kernels.TmlFa4Fwd.Thread
