-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstCopyProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyLaterProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerReload
import Kernels.TmlFa4Fwd.Flow.Code.Part015

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 4096 in
/-- The first warm pointer reload leaves its sibling lane-local cell current. -/
theorem WarmFirstPages.reloadKeyPointerPreservingOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : WarmFirstPages p l X g batch) :
    let head := (assignedCoordinates p batch (g/l.block)).2/6
    let ptr := fun lane => primingKRowPointer p batch head (warmFirstSlotRow p l g batch lane 0)
    ∃ done : SchedulerWarpReached l X g 1004
        (fun lane => warmKeyWords 0 (ptr lane) ++ warmFirstKeyPacked p l g batch lane)
        c.shuffles c.votes c.ends,
      ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (done.pos lane) 977
        (pointerSaveAccess l (warpLane l g lane) 0 1)
        (b64 (primingKRowPointer p batch head (warmFirstSlotRow p l g batch lane 1))).toBytes := by
  dsimp only
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let ptr := fun lane => primingKRowPointer p batch head (warmFirstSlotRow p l g batch lane 0)
  let addr := l.localBase+32
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hAddr : addr+warmKFirstReload.offset < 2^64 := by
    have h := hp.localMemory.2.1
    change l.localBase+32+0 < 2^64
    omega
  have hAlign : (addr+warmKFirstReload.offset)%8 = 0 := by
    have h := hp.localMemory.1
    change (l.localBase+32+0)%8 = 0
    omega
  have hPtr (lane : Nat) : ptr lane < 2^64 := by
    let row := warmFirstSlotRow p l g batch lane 0
    have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row) hb)
      (Nat.mod_lt row (by decide)) hh
    have hEq : sourceScratchPayload (primingScratchPage p batch row) (row%16)
        p.kLayout.pageStride p.kLayout.rowStride
        (p.kLayout.base+2*(head*p.kLayout.headStride)) = ptr lane := h.1
    exact hEq ▸ h.2.1
  obtain ⟨saved,hSaved⟩ := c.saveKeyPointersOfMaximal hp hMax hg hw hb hLo hHi
  obtain ⟨ready,hReady⟩ := warmFirstKeyPackFrameOfSaved hp hb hLo hHi hTrips saved
  have hFresh : ∀ lane < 32, ∀ pair ∈ warmFirstKeyPacked p l g batch lane,
      pair.1 ≠ warmKFirstReload.lowReg ∧ pair.1 ≠ warmKFirstReload.highReg := by
    intro lane _ pair hm
    have h : ((warmFirstKeyPacked p l g batch lane).map Prod.fst).all
        (fun r => decide (r ≠ warmKFirstReload.lowReg ∧ r ≠ warmKFirstReload.highReg)) = true := rfl
    exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  have hCell (lane : Nat) (hl : lane < 32) :
      PrimingCellValue X (warpLane l g lane) (ready.pos lane) 977
        (warmKFirstReload.cell (warpLane l g lane) addr) (b64 (ptr lane)).toBytes := by
    rw [hReady]
    exact hSaved lane hl 0
  obtain ⟨done,_,hKeep⟩ := warmKFirstReload.warpReadPreservingOfMaximal hp hMax hg (by decide)
    Flow.code_1003 hAddr hAlign (by decide) ptr (fun lane _ => hPtr lane) ready
    (fun _ _ => by simp [addr,warmKFirstReload,warmFirstKeyPacked,warmFirstKeyCarry,
      warmFirstPagesFrame,
      warmFirstFrame,openingWarmPublishedFrame,openingWarmFrame,warmStartFrame,
      warmPageRoots,warmLaneRoots]) hFresh hCell
  refine ⟨done,fun lane hl => (hKeep lane hl).2 ?_⟩
  rw [hReady]
  exact hSaved lane hl 1

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
