-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionCuQProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionFirstRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hLo : 8 ≤ warpIndex l g)
include hp hMax hg hLo

private theorem firstWarpCursor (hHi : warpIndex l g < 12) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 7762
      (fun lane => firstShuffleFacts p l (warpLane l g lane)) 3 0 ends) := by
  classical
  let thread := warpLane l g
  let F := fun lane => firstShuffleFacts p l (thread lane)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hC (lane : Nat) (hl : lane < 32) : ∃ j t u o,
      0 < j ∧ j ≤ (X.tr (thread lane)).length ∧ Softmax.beforeFirstScan X (thread lane) j ∧
      (j = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      At u 7762 (F lane) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take j) (some t) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) t u := by
    obtain ⟨hSame, _⟩ := Step.sameWarp_lane hBlock hg hl
    have hEq : warpIndex l g = warpIndex l (thread lane) := hSame.2
    exact firstShuffleCursorOfMaximal hp hMax hSame.1.2.1
      (hEq ▸ hLo) (hEq ▸ hHi) (hProtected _)
  let _ : Inhabited TState := ⟨{}⟩
  choose! j t u o hPos hBound hCount hReady hAt hPrefix hTail hLocal using hC
  exact ⟨o,⟨⟨⟨j,t,u,⟨fun lane hl => (hCount lane hl).1,fun lane hl => (hCount lane hl).2⟩,
    hTail,hLocal,hAt⟩,hPos,hBound,hReady,hPrefix⟩⟩⟩

/-- The first correction scan's adjacent endpoint exchange is an actual warp step. -/
theorem firstGroupDownOfMaximal (hHi : warpIndex l g < 12) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 7763
      (fun lane =>
        (5869,b32 (firstSchedulerWord p (shflSource .down lane 1 31).1)) ::
          firstShuffleFacts p l (warpLane l g lane)) 4 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := firstWarpCursor hp hMax hg hLo hHi hProtected
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨down⟩ := cur.consumeShuffle (dst := 5869) hp hMax hg .down
    (fun lane => b32 (firstSchedulerWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [firstShuffleFacts,afterCreditFacts,creditFacts,entryFacts,
      nonzeroBarrierFacts,abiFacts])
    (fun lane hl => by
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      simpa only [hLane] using firstShuffleOut hp (cur.checkpoint lane hl))
  exact ⟨ends,⟨down⟩⟩

/-- In a maximal execution the correction warp takes its true first-group scheduler branch
after all lanes perform their first CuQ exchange and the five inclusive scan rounds. -/
theorem firstGroupRouteOfMaximal (hHi : warpIndex l g < 12) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 7864 else 7807)
      (correctionFirstRouteFacts p l g) 10 0 ends) := by
  obtain ⟨ends,⟨down⟩⟩ := firstGroupDownOfMaximal hp hMax hg hLo hHi hProtected
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨first⟩ := down.advanceLocal
    (G := fun lane => firstCorrectionScanFacts p l (warpLane l g lane)) (pc' := 7781) (by
    intro lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    obtain ⟨_, u, hu, hU⟩ := correctionFirstTiles hp
      (show At (down.state lane) 7763
        ((5869, b32 (firstSchedulerWord p (shflSource .down
          (laneOf l (warpLane l g lane)) 1 31).1)) ::
           firstShuffleFacts p l (warpLane l g lane)) by
        rw [hLane]
        exact down.checkpoint lane hl)
    exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨scan⟩ := correctionFirstScanOfMaximal hp hMax hg first
  exact ⟨ends,correctionFirstRouteOfMaximal hp hMax hg scan⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
