-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionScanProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFallbackWarp
public import Kernels.TmlFa4Fwd.Proof.CorrectionActiveCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- Every active correction warp reaches the populated group that contains its assigned tile. -/
theorem activeGroupOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hCuQ : DrainCuQProtected p X) (hWork : g/l.block < tilePrefix p p.batch*p.heads) :
    ∃ first shuffles ends, tilePrefix p first*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (min p.batch (first+31))*p.heads ∧
      Nonempty (SchedulerWarpReached l X g 7864 (correctionGroupEntry p l g first)
        shuffles 0 ends) := by
  obtain ⟨ends,route⟩ := firstGroupRouteOfMaximal hp hMax hg hLo hHi hCuQ
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads
  · rw [ite_eq_left hFirst] at route
    obtain ⟨cur⟩ := route
    refine ⟨0,10,ends,by simp [tilePrefix],hFirst,?_⟩
    apply cur.advanceLocal
    intro lane hl
    have ht := cur.checkpoint lane hl
    have hR := ht.2.2.2.2
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hSum := groupTiles_eq p (Nat.zero_le p.batch) (show (32 : Nat) ≤ 32 by decide)
    have he : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) = tilePrefix p (min p.batch 31) :=
      by simpa [tilePrefix] using hSum
    have hTotal := hR.2.2.2.1
    rw [← he] at hTotal
    have hTiles := hR.2.2.2.2.2.1
    rw [hLane] at hTiles
    exact ⟨_,.refl,ht.mono ⟨hR.1,hR.2.1,hTotal,hR.2.2.2.2.1,hTiles,
      hR.2.2.2.2.2.2.1,hR.2.2.1,hR.2.2.2.2.2.2.2.2⟩⟩
  · rw [ite_eq_right hFirst] at route
    obtain ⟨cur⟩ := route
    obtain ⟨first,shuffles,hPast,hCut,⟨next⟩⟩ :=
      Fallback.activeSearchOfMaximal hp hMax hg hWork (Nat.le_of_not_gt hFirst) hCuQ cur
    refine ⟨first,shuffles,ends,hPast,hCut,?_⟩
    apply next.advanceLocal
    intro lane hl
    have ht := next.checkpoint lane hl
    have h := ht.2.2.2.2
    have hPart := h.2.2.1
    rw [← prefixWindow_warp _ hl] at hPart
    exact ⟨_,.refl,ht.mono ⟨h.2.2.2.1,h.2.2.2.2.2.2.1,h.2.1,hPart,
      h.2.2.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hwLo : 8 ≤ warpIndex l g) (hwHi : warpIndex l g < 12) (hCuQ : DrainCuQProtected p X)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hg hwLo hwHi hCuQ hBatch hLo

/-- The actual group ballot selects the specified active tile's request on the correction warp. -/
theorem activeBatchOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ first shuffles ends, first ≤ batch ∧ batch < first+31 ∧
      Nonempty (SchedulerWarpReached l X g 7878 (correctionChosenFacts p l g first batch)
        shuffles 1 ends) := by
  have hEnd : batch+1 ≤ p.batch := hBatch
  have hWork := hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hEnd))
  obtain ⟨first,shuffles,ends,hPast,hCut,⟨cur⟩⟩ :=
    activeGroupOfMaximal hp hMax hg hwLo hwHi hCuQ hWork
  have hFirst : first ≤ batch := by
    by_contra! h
    exact (Nat.not_lt_of_ge hPast)
      (hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p h)))
  have hGroup : batch < first+31 := by
    by_contra! h
    have hLe : min p.batch (first+31) ≤ batch := (Nat.min_le_right ..).trans h
    exact (Nat.not_lt_of_ge hLo)
      (hCut.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hLe)))
  obtain ⟨ready,hPos,hBefore⟩ :=
    correctionGroupBallotReadyPreserving hp hFirst hGroup hBatch hLo hHi cur.toSchedulerWarpAt
  exact ⟨first,shuffles,ends,hFirst,hGroup,
    correctionSelectBatchOfMaximal hp hMax hg hFirst hGroup hBatch
      (cur.reframe ready hPos hBefore)⟩

/-- A scheduled correction warp reaches the assigned active tile through its actual exchanges. -/
theorem activeTileOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ shuffles ends, Nonempty (SchedulerWarpReached l X g 7932
      (correctionActiveTileFacts p l g batch) shuffles 1 ends) := by
  obtain ⟨_,_,ends,hFirst,hGroup,⟨chosen⟩⟩ :=
    activeBatchOfMaximal hp hMax hg hwLo hwHi hCuQ hBatch hLo hHi
  obtain ⟨pref⟩ := correctionSelectedPrefixOfMaximal hp hMax hg hFirst hGroup hBatch chosen
  obtain ⟨coordinates⟩ :=
    correctionSelectedCoordinatesOfMaximal hp hMax hg hFirst hGroup hBatch hLo hHi pref
  obtain ⟨ready,hPos,hBefore⟩ :=
    correctionActiveCoordinatesPreserving hp hBatch hLo hHi coordinates.toSchedulerWarpAt
  exact ⟨_,ends,⟨coordinates.reframe ready hPos hBefore⟩⟩

end PTX.Kernels.TmlFa4Fwd.Correction
