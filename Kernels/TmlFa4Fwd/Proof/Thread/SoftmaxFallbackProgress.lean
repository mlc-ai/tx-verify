-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScanProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- A reached idle softmax search exhausts its requests after following the real group reads and
warp exchanges. Each continued group strictly decreases the number of requests left to scan. -/
theorem idleFallbackSearchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {warp : Fin 8} {ends : Nat → Option TState}
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block)
    (first shuffles : Nat) (hFirst : first < p.batch)
    (cur : SchedulerWarpReached l X g 3158 (fun lane =>
      fallbackScanFacts p l (warpLane l g lane) warp first
        (tilePrefix p (min p.batch (first + 31)) * p.heads)) shuffles 0 ends) :
    ∃ last count, p.batch ≤ last + 31 ∧ Nonempty (SchedulerWarpReached l X g 3209 (fun lane =>
      fallbackAdvanceFacts p l (warpLane l g lane) warp last
        (tilePrefix p (min p.batch (last + 31)) * p.heads)) count 0 ends) := by
  obtain ⟨next, hPos, hBefore⟩ := warpFallbackAdvancePreserving hp hFirst cur.toSchedulerWarpAt
  have hNext := cur.reframe next hPos hBefore
  by_cases hDone : p.batch ≤ first + 31
  · rw [ite_eq_left hDone] at hNext
    exact ⟨first, shuffles, hDone, ⟨hNext⟩⟩
  · rw [ite_eq_right hDone] at hNext
    have hMore : first + 31 < p.batch := Nat.lt_of_not_ge hDone
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
    have hCut : tilePrefix p (min p.batch (first + 31 + 31)) * p.heads ≤ g / l.block :=
      (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left _ _))).trans hIdle
    simp only [ite_eq_left hCut] at hRoute
    obtain ⟨again⟩ := hRoute
    exact idleFallbackSearchOfMaximal hp hMax hg hProtected hIdle (first + 31)
      (shuffles + 1 + 5 + 1) hMore again
termination_by p.batch - first
decreasing_by omega

/-- The idle warp's first scan and every later scan reach its exhausted scheduler boundary. -/
theorem idleSoftmaxSearchExhaustedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hProtected : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    let warp : Fin 8 := ⟨warpIndex l g, hw⟩
    ∃ last count ends, p.batch ≤ last + 31 ∧ Nonempty (SchedulerWarpReached l X g 3209
      (fun lane => fallbackAdvanceFacts p l (warpLane l g lane) warp last
        (tilePrefix p (min p.batch (last + 31)) * p.heads)) count 0 ends) := by
  dsimp only
  obtain ⟨ends, ⟨route⟩⟩ := firstGroupRouteOfMaximal hp hMax hg hw hProtected
  have hCut : tilePrefix p (min p.batch 31) * p.heads ≤ g / l.block :=
    (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.min_le_left _ _))).trans hIdle
  rw [ite_eq_right (Nat.not_lt_of_ge hCut)] at route
  obtain ⟨next, hPos, hBefore⟩ := warpFallbackStartPreserving hp hg route.toSchedulerWarpAt
  obtain ⟨last, count, hDone, cur⟩ :=
    idleFallbackSearchOfMaximal hp hMax hg hProtected hIdle 0 10 hp.shape.1
      (route.reframe next hPos hBefore)
  exact ⟨last, count, ends, hDone, cur⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
