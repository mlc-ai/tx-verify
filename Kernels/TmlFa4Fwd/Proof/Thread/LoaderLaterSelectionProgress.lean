-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScanProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderLaterRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

private theorem fallbackStepOfMaximal {g warp first shuffles : Nat} (hg : g < l.threads)
    (hMore : first + 31 < p.batch) (hCuQ : DrainCuQProtected p X) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 234 (loaderFallbackFacts p l g warp first) shuffles 0 ends) :
    let next := first + 31
    let limit := tilePrefix p (min p.batch (next + 31)) * p.heads
    if limit ≤ g / l.block then
      Nonempty (SchedulerWarpReached l X g 234
        (loaderFallbackFacts p l g warp next) (shuffles + 7) 0 ends)
    else
      Nonempty (SchedulerWarpReached l X g 288
        (loaderLaterChoiceFacts p l g warp next) (shuffles + 7) 0 ends) := by
  dsimp only
  have hFirst : first < p.batch := by omega
  have hAdvance := loaderFallbackAdvanceAtPreserving hp hFirst cur.toSchedulerWarpAt
  rw [ite_eq_right (Nat.not_le_of_gt hMore)] at hAdvance
  obtain ⟨entry,hPos,hBefore⟩ := hAdvance
  obtain ⟨read⟩ := loaderLaterWarpCuQOfMaximal hp hMax hg hMore hCuQ
    (cur.reframe entry hPos hBefore)
  obtain ⟨scan⟩ := loaderLaterScanOfMaximal hp hMax hg hMore read
  exact loaderLaterRouteOfMaximal hp hMax hg hMore scan

private theorem fallbackGroupsOfMaximal {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (group : Nat) (hMore : 31 * (group + 1) < p.batch)
    (hLo : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 234
      (loaderFallbackFacts p l g (warpIndex l g) (31 * group)) (10 + 7 * group) 0 ends) := by
  induction group with
  | zero =>
    have hRoute := firstRouteOfMaximal hp hMax hg hw hCuQ
    have hCut : ¬g / l.block < tilePrefix p (min p.batch 31) * p.heads := by
      rw [Nat.min_eq_right (by simpa using hMore.le)]
      exact Nat.not_lt_of_ge (by simpa using hLo)
    rw [ite_eq_right hCut] at hRoute
    obtain ⟨ends,⟨cur⟩⟩ := hRoute
    obtain ⟨start,hPos,hBefore⟩ := loaderFallbackStartAtPreserving hp hg cur.toSchedulerWarpAt
    exact ⟨ends,⟨cur.reframe start hPos hBefore⟩⟩
  | succ group ih =>
    let old := 31 * group
    have hNext : old + 31 = 31 * (group + 1) := by dsimp [old]; omega
    have hNextMore : old + 31 < p.batch := by omega
    have hClip : min p.batch (old + 31 + 31) = 31 * (group.succ + 1) := by
      have hEnd : old + 31 + 31 = 31 * (group.succ + 1) := by omega
      rw [hEnd, Nat.min_eq_right hMore.le]
    have hBefore : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block :=
      (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega))).trans hLo
    obtain ⟨ends,⟨cur⟩⟩ := ih (hNext ▸ hNextMore) hBefore
    have hNext := fallbackStepOfMaximal hp hMax hg hNextMore hCuQ cur
    dsimp only at hNext
    rw [show 31 * group + 31 + 31 = old + 31 + 31 from rfl, hClip, ite_eq_left hLo] at hNext
    refine ⟨ends,?_⟩
    simpa only [show old + 31 = 31 * (group + 1) by omega,
      show 10 + 7 * group + 7 = 10 + 7 * (group + 1) by omega,
      Nat.succ_eq_add_one] using hNext

/-- An active later loader group reaches its actual selection boundary in every lane. -/
theorem laterLoaderGroupOfMaximal {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (group : Nat) (hMore : 31 * (group + 1) < p.batch)
    (hLo : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (min p.batch (31 * (group + 2))) * p.heads) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 288
      (loaderLaterChoiceFacts p l g (warpIndex l g) (31 * (group + 1)))
      (10 + 7 * (group + 1)) 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := fallbackGroupsOfMaximal hp hMax hg hw hCuQ group hMore hLo
  have hMore' : 31 * group + 31 < p.batch := by omega
  have hNext := fallbackStepOfMaximal hp hMax hg hMore' hCuQ cur
  dsimp only at hNext
  rw [show 31 * group + 31 + 31 = 31 * (group + 2) by omega,
    ite_eq_right (Nat.not_le_of_lt hHi)] at hNext
  exact ⟨ends,by simpa only [show 31 * group + 31 = 31 * (group + 1) by omega,
    show 10 + 7 * group + 7 = 10 + 7 * (group + 1) by omega] using hNext⟩

/-- A later idle group scans through its last request and reaches the actual terminal backedge. -/
theorem laterIdleLoaderGroupOfMaximal {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (group : Nat) (hMore : 31 * (group + 1) < p.batch)
    (hLast : p.batch ≤ 31 * (group + 2)) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 234
      (loaderFallbackFacts p l g (warpIndex l g) (31 * (group + 1)))
      (10 + 7 * (group + 1)) 0 ends) := by
  have hLo : tilePrefix p (31 * (group + 1)) * p.heads ≤ g / l.block :=
    (Nat.mul_le_mul_right _ (tilePrefix_mono p hMore.le)).trans hIdle
  obtain ⟨ends,⟨cur⟩⟩ := fallbackGroupsOfMaximal hp hMax hg hw hCuQ group hMore hLo
  have hMore' : 31 * group + 31 < p.batch := by omega
  have hNext := fallbackStepOfMaximal hp hMax hg hMore' hCuQ cur
  dsimp only at hNext
  rw [show 31 * group + 31 + 31 = 31 * (group + 2) by omega,
    Nat.min_eq_left hLast, ite_eq_left hIdle] at hNext
  exact ⟨ends,by simpa only [show 31 * group + 31 = 31 * (group + 1) by omega,
    show 10 + 7 * group + 7 = 10 + 7 * (group + 1) by omega] using hNext⟩

end PTX.Kernels.TmlFa4Fwd.Loader
