-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundExit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader Protocol.Loader
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A loader lane at the drain entry with ring cursor `2*trips`, whose recurring
publications all lie below that cursor, exits once the MMA has released every ring use and,
for warp 14, the final query stage. -/
theorem loaderExitOfDrainEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch n : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hb : batch < p.batch) (hn : 1 ≤ n)
    (hEntry : CacheDrainEntry p l X g (2*n))
    (hUses : ∀ lane < 32, RecurringUsesBelow X (warpLane l g lane) (2*n))
    (hReleased : CacheUsesReleased l X g (2*n+3))
    (hQuery : warpIndex l g = 14 → UnitRelease X (secondQueryEmpty l (g/l.block))) :
    Thread.Exited X g := by
  have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hUse := hUses (laneOf l g) (Nat.mod_lt _ (by decide))
  rw [hSelf] at hUse
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  apply cacheLoaderExitOfCompletedCredits hp hMax hg hw (hFrame.metadataProtected hp).1 hActive
    hEntry _ hQuery
  apply cacheReleaseCountsOfReleases hp hMax hg hw hUse (by omega)
  intro slot
  have hs := slot.isLt
  let use := 2*n+(3-(2*n)%3+slot.val)%3
  have hStage : kvUseStage use = slot := Fin.ext (by rw [kvUseStage_val]; dsimp only [use]; omega)
  have h := hReleased use (by dsimp only [use]; omega) (by dsimp only [use]; omega)
  rw [hStage] at h
  have hCount : (2*n+(2-slot.val))/3 = use/3 := by dsimp only [use]; omega
  rw [hCount]
  exact h

end PTX.Kernels.TmlFa4Fwd.Progress
