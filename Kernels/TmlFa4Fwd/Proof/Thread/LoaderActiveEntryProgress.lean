-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActiveSelectionProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderActiveEntry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem activePrefixOfMaximal {g warp first batch shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first ≤ batch) (hGroup : batch < first+31) (hBatch : batch < p.batch)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 302
      (loaderChosenFacts p l g warp first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 306 (loaderPrefixFacts p l g warp first batch)
      (shuffles + if first < batch then 1 else 0) votes ends) := by
  by_cases hEq : batch = first
  · rw [ite_eq_right (by omega : ¬ first < batch),Nat.add_zero]
    exact cur.advanceLocal (fun lane hl =>
      loaderSelectedPrefixZeroLocal lane hEq (cur.checkpoint lane hl))
  · have hLess : first < batch := by omega
    rw [ite_eq_left hLess]
    let idx := batch-first-1
    let part := fun lane => ∑ j ∈ Finset.range (lane+1), groupLaneTiles p first j
    let carry := fun lane => (1752,b32 idx) :: loaderChosenFacts p l g warp first batch lane
    obtain ⟨ready⟩ := cur.advanceLocal (G := carry) (pc' := 304) (fun lane hl =>
      loaderSelectedPrefixIdxLocal hFirst hGroup hEq lane (cur.checkpoint lane hl))
    obtain ⟨read⟩ := ready.consumeShuffle (dst := 1753) hp hMax hg .idx
      (fun lane => b32 (part lane)) (fun _ => idx) (fun _ => 31)
      (fun lane _ pair hm he => by
        have hMem := List.mem_map_of_mem (f := Prod.fst) hm
        rw [he] at hMem
        exact (of_decide_eq_true rfl : 1753 ∉ (carry lane).map Prod.fst) hMem)
      (fun lane hl => by
        have ht := ready.checkpoint lane hl
        have hv := holds_lookup ht.2.2.2.2 (show (carry lane).lookup 7163 =
          some (b32 (part lane)) from rfl)
        exact loaderPrefixIdxTemplate hp (show idx < 32 by dsimp [idx]; omega)
          (ht.mono ⟨ht.2.2.2.2.1,hv,trivial⟩))
    exact read.advanceLocal (fun lane hl =>
      loaderSelectedPrefixReturnLocal hp hFirst hGroup hBatch hLess lane (read.checkpoint lane hl))

private theorem activeCoordinatesOfMaximal {g warp first batch shuffles votes : Nat}
    (hg : g < l.threads) (hFirst : first ≤ batch) (hGroup : batch < first+31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 306
      (loaderPrefixFacts p l g warp first batch) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 311 (loaderCoordinateFacts p l g warp first batch)
      (shuffles+1) votes ends) := by
  let carry := loaderCoordCarry p l g warp first batch
  let idx := batch-first
  obtain ⟨ready⟩ := cur.advanceLocal (G := carry) (pc' := 308)
    (fun lane hl => loaderCoordinatesPrepare hp (cur.checkpoint lane hl))
  obtain ⟨read⟩ := ready.consumeShuffle (dst := 1754) hp hMax hg .idx
    (fun lane => b32 (groupLaneTiles p first lane)) (fun _ => idx) (fun _ => 31)
    (fun lane _ pair hm he => by
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [he] at hMem
      exact (of_decide_eq_true rfl : 1754 ∉ (carry lane).map Prod.fst) hMem)
    (fun lane hl => by
      have ht := ready.checkpoint lane hl
      have hIdx := holds_lookup ht.2.2.2.2
        (show (carry lane).lookup 1080 = some (b32 idx) from rfl)
      have hCount := holds_lookup ht.2.2.2.2 (show (carry lane).lookup 7162 =
        some (b32 (groupLaneTiles p first lane)) from rfl)
      exact loaderTileCountTemplate hp (show idx < 32 by dsimp [idx]; omega)
        (ht.mono ⟨hIdx,hCount,trivial⟩))
  exact read.advanceLocal (fun lane hl =>
    loaderCoordinatesReturned hp hg hl hFirst hGroup hBatch hLo hHi (read.checkpoint lane hl))

/-- Every active loader warp establishes its assigned request's actual coordinates. -/
theorem selectedActiveCoordinatesOfMaximal {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) {batch : Nat} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 311
      (loaderCoordinateFacts p l g (warpIndex l g) (31 * (batch / 31)) batch)
      (10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1) 1 ends) := by
  have hPart := Nat.div_add_mod batch 31
  have hRem := Nat.mod_lt batch (show 0 < 31 by decide)
  have hFirst : 31 * (batch / 31) ≤ batch := by omega
  have hGroup : batch < 31 * (batch / 31) + 31 := by omega
  obtain ⟨ends,⟨chosen⟩⟩ := selectedBatchOfMaximal hp hMax hg hw hCuQ hBatch hLo hHi
  obtain ⟨prior⟩ := activePrefixOfMaximal hp hMax hg hFirst hGroup hBatch chosen
  obtain ⟨coords⟩ := activeCoordinatesOfMaximal hp hMax hg hFirst hGroup hBatch hLo hHi prior
  exact ⟨ends,⟨coords⟩⟩

end PTX.Kernels.TmlFa4Fwd.Loader
