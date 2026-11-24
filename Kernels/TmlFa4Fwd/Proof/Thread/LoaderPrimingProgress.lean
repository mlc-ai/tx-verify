-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveReadProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKActive

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The register facts retained while reaching the first cache-address preparation. -/
def loaderPrimingFrontierFacts (p : Params) (l : Launch) (g batch lane : Nat) :
    List (Nat × Value) :=
  let coords := assignedCoordinates p batch (g/l.block)
  primingKAddressFacts p l batch coords.2 coords.1 (warpIndex l g) lane ++
    ((7170,b32 batch) :: warmLaneRoots l (warpLane l g lane % l.block))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hMax writes

private theorem primingAddressesFromCoordinates {g first batch shuffles votes : Nat}
    (hg : g < l.threads) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) {ends : Nat → Option TState}
    (coords : SchedulerWarpReached l X g 311
      (loaderCoordinateFacts p l g (warpIndex l g) first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      shuffles votes ends) := by
  obtain ⟨entry,hPos,hBefore⟩ :=
    primingKActiveEntryWithLaneRootsPreserving hp hBatch hLo hHi coords.toSchedulerWarpAt
  let roots := fun lane => warmLaneRoots l (warpLane l g lane % l.block)
  let abi := fun lane => primingKActiveAbi p l (warpIndex l g) ++ roots lane
  have hExtras (lane : Nat) (_ : lane < 32) : ActiveReadExtra (abi lane) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro pair hm h
      have hMap := List.mem_map_of_mem (f := Prod.fst) hm
      rw [h] at hMap
      exact (of_decide_eq_true rfl : 1799 ∉ (abi lane).map Prod.fst) hMap
    · intro pair hm h
      have hMap := List.mem_map_of_mem (f := Prod.fst) hm
      rw [h] at hMap
      exact (of_decide_eq_true rfl : 1800 ∉ (abi lane).map Prod.fst) hMap
    · intro pair hm h
      have hMap := List.mem_map_of_mem (f := Prod.fst) hm
      rw [h] at hMap
      exact (of_decide_eq_true rfl : 1086 ∉ (abi lane).map Prod.fst) hMap
    · set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨metadata⟩ := recordActiveMetadataWithFrame hp hMax writes hg hBatch
    (coords.reframe entry hPos hBefore) hExtras
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  apply metadata.advanceLocal
  intro lane hl
  have ht := metadata.checkpoint lane hl
  have hFrame := primingKActiveMetadataFrame hp hg hl hTile (extra := roots lane) (by
    simpa only [loaderInitialMetadataFrame,List.append_assoc,abi] using ht)
  exact primingKActiveToAddressLaneWithExtra hp hBatch hTile
    (by set_option maxRecDepth 100000 in kernel_rfl) hFrame

omit hp hMax writes in
private theorem primingScratchFromAddresses {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m)
    {g batch shuffles votes : Nat} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {ends : Nat → Option TState}
    (addresses : SchedulerWarpReached l X g 415
      (loaderPrimingFrontierFacts p l g batch) shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    let keyTile := Mma.trips p batch coords.1 - 1
    128 * keyTile + 127 < 2 ^ 31 ∧ Nonempty (SchedulerWarpReached l X g 488
      (primingKInitialScratchFacts p l batch (coords.2 / 6) keyTile (warpIndex l g))
      shuffles votes ends) := by
  let coords := assignedCoordinates p batch (g/l.block)
  let keyTile := Mma.trips p batch coords.1 - 1
  let warp := warpIndex l g
  obtain ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hHeadSigned : coords.2 < 2^31 := hHead.trans hp.heads_signed
  obtain ⟨visible⟩ := addresses.advanceLocal (pc' := 439)
    (G := primingKVisibleFacts p l batch (coords.2/6) coords.1 warp) (fun lane hl =>
      primingKAddressToVisibleLane hp hBatch hHeadSigned hTile
        ((addresses.checkpoint lane hl).mono
          ((holds_append ..).mp (addresses.checkpoint lane hl).2.2.2.2).1))
  obtain ⟨trips⟩ := visible.advanceLocal (pc' := 477)
    (G := primingKTripFacts p l batch (coords.2/6) coords.1 warp) (fun lane hl =>
      primingKTripSeedLane hp hBatch hTile (visible.checkpoint lane hl))
  have hLimit : 128*keyTile+127 < 2^31 :=
    (primingKEnterScratchLane (g := warpLane l g 0) hp hBatch hTile
      (trips.checkpoint 0 (by decide))).1
  exact ⟨hLimit,trips.advanceLocal (fun lane hl =>
    (primingKEnterScratchLane hp hBatch hTile (trips.checkpoint lane hl)).2)⟩

/-- Every active loader reaches its first cache-address preparation with the selected
request's exact coordinates and metadata. -/
theorem selectedPrimingAddressesOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      (10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1) 1 ends) := by
  obtain ⟨ends,⟨coords⟩⟩ := selectedActiveCoordinatesOfMaximal hp hMax hg hw
    (hp.cuQ_protected writes) hBatch hLo hHi
  exact ⟨ends,primingAddressesFromCoordinates hp hMax writes hg hBatch hLo hHi coords⟩

/-- Every active loader reaches the actual first scratch iteration with the paged K/V
root and selected request geometry. -/
theorem selectedPrimingScratchOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    let coords := assignedCoordinates p batch (g / l.block)
    let keyTile := Mma.trips p batch coords.1 - 1
    128 * keyTile + 127 < 2 ^ 31 ∧
      ∃ ends, Nonempty (SchedulerWarpReached l X g 488
        (primingKInitialScratchFacts p l batch (coords.2 / 6) keyTile (warpIndex l g))
        (10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1) 1 ends) := by
  obtain ⟨ends,⟨addresses⟩⟩ :=
    selectedPrimingAddressesOfMaximal hp hMax writes hg hw hBatch hLo hHi
  obtain ⟨hLimit,hScratch⟩ := primingScratchFromAddresses hp hBatch hLo hHi addresses
  exact ⟨hLimit,ends,hScratch⟩

end PTX.Kernels.TmlFa4Fwd.Loader
