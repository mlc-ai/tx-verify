-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxFallbackProgress
import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackSearch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- A reached active softmax search selects its containing group after the real reads and
warp exchanges. Each continued group strictly decreases the number of requests left to scan. -/
theorem activeFallbackSearchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {warp : Fin 8} {ends : Nat → Option TState}
    (hProtected : DrainCuQProtected p X) (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (first shuffles : Nat) (hFirst : first < p.batch)
    (hPast : tilePrefix p (min p.batch (first+31)) * p.heads ≤ g/l.block)
    (cur : SchedulerWarpReached l X g 3158 (fun lane =>
      fallbackScanFacts p l (warpLane l g lane) warp first
        (tilePrefix p (min p.batch (first + 31)) * p.heads)) shuffles 0 ends) :
    ∃ selected count, tilePrefix p selected * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (min p.batch (selected+31)) * p.heads ∧
      Nonempty (SchedulerWarpReached l X g 3212
        (fun lane => groupRouteFacts p l (warpLane l g lane) warp selected) count 0 ends) := by
  obtain ⟨next,hPos,hBefore⟩ := warpFallbackAdvancePreserving hp hFirst cur.toSchedulerWarpAt
  have hNext := cur.reframe next hPos hBefore
  have hMore : first + 31 < p.batch := by
    by_contra! hNo
    rw [Nat.min_eq_left hNo] at hPast
    omega
  rw [ite_eq_right (Nat.not_le_of_lt hMore)] at hNext
  obtain ⟨down⟩ := warpFallbackDownOfMaximal hp hMax hg hMore hProtected hNext
  obtain ⟨tiles, hTilesPos, hTilesBefore⟩ :=
    warpFallbackTilesPreserving hp hg hMore down.toSchedulerWarpAt
  let tileCursor := down.reframe tiles hTilesPos hTilesBefore
  obtain ⟨start, hStartPos, hStartBefore⟩ := warpFallbackFoldStartPreserving tiles
  obtain ⟨fold⟩ := warpFallbackFoldOfMaximal hp hMax hg hMore.le
    (tileCursor.reframe start hStartPos hStartBefore)
  have hFold : SchedulerWarpReached l X g 3207 (fun lane =>
      fallbackFoldFacts p l (warpLane l g lane) warp first
        (tilePrefix p (first + 31) * p.heads) 5) (shuffles + 1 + 5) 0 ends := by
    simpa only [Nat.min_eq_right hMore.le] using fold
  have hRoute := warpFallbackRouteOfMaximal hp hMax hg hMore hFold
  dsimp only at hRoute
  by_cases hCut : tilePrefix p (min p.batch (first+31+31)) * p.heads ≤ g/l.block
  · simp only [ite_eq_left hCut] at hRoute
    obtain ⟨again⟩ := hRoute
    exact activeFallbackSearchOfMaximal hp hMax hg hProtected hWork (first+31)
      (shuffles+1+5+1) hMore hCut again
  · simp only [ite_eq_right hCut] at hRoute
    exact ⟨first+31,shuffles+1+5+1,
      (Nat.min_eq_right hMore.le) ▸ hPast,Nat.lt_of_not_ge hCut,hRoute⟩
termination_by p.batch - first
decreasing_by omega

/-- The maximal scheduler reaches the containing request group, using only recorded
protected reads and collective exchanges. -/
theorem activeGroupOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hProtected : DrainCuQProtected p X) (hWork : g/l.block < tilePrefix p p.batch * p.heads) :
    let warp : Fin 8 := ⟨warpIndex l g,hw⟩
    ∃ selected count ends, tilePrefix p selected * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (min p.batch (selected+31)) * p.heads ∧
      Nonempty (SchedulerWarpReached l X g 3212
        (fun lane => groupRouteFacts p l (warpLane l g lane) warp selected) count 0 ends) := by
  dsimp only
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  obtain ⟨ends,route⟩ := firstGroupRouteOfMaximal hp hMax hg hw hProtected
  by_cases hFirst : g/l.block < tilePrefix p (min p.batch 31) * p.heads
  · rw [ite_eq_left hFirst] at route
    obtain ⟨route⟩ := route
    have hBlock : l.block % 32 = 0 := by rw [hp.block]
    obtain ⟨result⟩ := route.advanceLocal (pc' := 3212)
      (G := fun lane => groupRouteFacts p l (warpLane l g lane) warp 0) (by
        intro lane hl
        have hAt : At (route.state lane) 3212 (firstRouteFacts p l g warp lane) := by
          simpa only [show g / l.block < tilePrefix p (min p.batch 31) * p.heads from hFirst,
            ↓reduceIte] using route.checkpoint lane hl
        have hs := hAt.2.2.2.2
        have hHeads := hs.2.2.2.2.2.1
        have hLane := hs.2.2.2.2.2.2.2.1
        have hEntry := hs.2.2.2.2.2.2.2.2.2
        have hTotal : (∑ i ∈ Finset.range 32, groupLaneTiles p 0 i) =
            tilePrefix p (min p.batch 31) := by
          simpa [tilePrefix] using groupTiles_eq p (Nat.zero_le _) (by decide : 32 ≤ 32)
        have hPrefix := hs.2.2.2.1
        change (route.state lane).regs 7241 =
          some (b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) at hPrefix
        rw [prefixWindow_warp _ hl] at hPrefix
        have hSame : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
        refine ⟨route.state lane, .refl, hAt.mono ?_⟩
        unfold groupRouteFacts fallbackBaseFrame
        rw [hSame]
        have hOwn := hs.2.2.2.2.1
        change (route.state lane).regs 7240 =
          some (b32 (groupLaneTiles p 0 (laneOf l (warpLane l g lane)))) at hOwn
        rw [hSame] at hLane hOwn
        exact ⟨hs.1, hs.2.1, hTotal.symm ▸ hs.2.2.1, hPrefix, hOwn, hHeads, hLane, hEntry⟩)
    exact ⟨0,10,ends,by simp [tilePrefix],hFirst,⟨result⟩⟩
  · rw [ite_eq_right hFirst] at route
    obtain ⟨route⟩ := route
    obtain ⟨start,hPos,hBefore⟩ := warpFallbackStartPreserving hp hg route.toSchedulerWarpAt
    obtain ⟨selected,count,hLo,hHi,result⟩ := activeFallbackSearchOfMaximal
      hp hMax hg hProtected hWork 0 10 hp.shape.1 (Nat.le_of_not_gt hFirst)
      (route.reframe start hPos hBefore)
    exact ⟨selected,count,ends,hLo,hHi,result⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
