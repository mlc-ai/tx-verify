-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScore
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveGroupProgress
import Kernels.TmlFa4Fwd.Proof.SoftmaxGroupCoordinates
import Kernels.TmlFa4Fwd.Proof.SoftmaxTileCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
include hp hMax hg

/-- A maximal active softmax warp selects the exact launch tile in any scheduler group. -/
theorem activeWarpOfMaximal (hw : warpIndex l g < 8) (hProtected : DrainCuQProtected p X)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ count ends, Nonempty (SchedulerWarpReached l X g 3274
      (fun _ => firstActiveTileFacts p l g ⟨warpIndex l g,hw⟩ batch) count 1 ends) := by
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  obtain ⟨first,ord,ends,hStart,hCut, ⟨route⟩⟩ :=
    activeGroupOfMaximal hp hMax hg hw hProtected hWork
  have hFirst : first ≤ batch := by
    by_contra! h
    exact (Nat.not_le_of_lt hHi) ((Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (show batch + 1 ≤ first by omega))).trans hStart)
  have hGroup : batch < first + 31 := by
    by_contra! h
    exact (Nat.not_le_of_lt hCut) ((Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p ((Nat.min_le_right _ _).trans h))).trans hLo)
  obtain ⟨chosen⟩ := groupChosenOfMaximal hp hMax hg hFirst hGroup hb hLo hHi route
  exact ⟨_,ends,groupActiveTileOfChosen hp hMax hg hFirst hGroup hb hLo hHi chosen⟩

/-- A softmax lane assigned to any request group records its
opening score acquire when the statistics and score objects admit the decoded polls. -/
theorem stageScoreAcquireOfMaximal (hw : warpIndex l g < 8) (hProtected : DrainCuQProtected p X)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCuQ : ∀ off ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*(batch+off))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k))
    (hAckReady : (¬ ∃ j, Thread.Scores.CreditAcquired X (g,j)) →
      OpeningPollReady X (waitLoc l g (stageOf ⟨warpIndex l g,hw⟩) 0) 1)
    (hScoreReady : (¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) (stageOf ⟨warpIndex l g,hw⟩)) →
      OpeningPollReady X (waitLoc l g (stageOf ⟨warpIndex l g,hw⟩) 1) 0) :
    ∃ j, Thread.Scores.FirstScoreAcquire l X (g,j) (stageOf ⟨warpIndex l g,hw⟩) := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  obtain ⟨_,ends,⟨w⟩⟩ :=
    activeWarpOfMaximal hp hMax hg warp.isLt hProtected hb hLo hHi
  let lane := laneOf l g
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hEq : warpLane l g lane = g := Step.warpLane_of_sameWarp hSelf
  let c : OpeningLaneCursor l X g 3274 (firstActiveTileFacts p l g warp batch) (ends lane) :=
    ⟨w.pos lane, w.before lane, w.state lane, w.positive lane hLane,
      by simpa only [hEq] using w.bounded lane hLane,
      by simpa only [hEq] using w.released lane hLane,
      by simpa only [hEq] using w.recorded lane hLane,
      by simpa only [hEq] using w.continuation lane hLane,
      by simpa only [hEq] using w.localSteps lane hLane, w.checkpoint lane hLane⟩
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨_,j,_,he,_,_⟩ := openingScorePollOfSelected hp hMax hg warp hb hTile c hCuQ hUsedK
    hAckReady hScoreReady
  exact ⟨j, Thread.Scores.FirstScoreAcquire.ofDecoded he⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
