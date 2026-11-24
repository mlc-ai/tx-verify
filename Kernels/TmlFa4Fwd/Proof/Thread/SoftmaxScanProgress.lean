-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxCuQProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleWarp
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainSearch
public import Lemmas.Step.WarpShuffleProgress
public import Lemmas.Flow.WarpScan
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleRoute

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

private theorem firstWarpCursor (hw : warpIndex l g < 8) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 3111
      (schedulerFirstWarpFacts p l g ⟨warpIndex l g,hw⟩) 3 0 ends) := by
  classical
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let thread := warpLane l g
  let F := schedulerFirstWarpFacts p l g warp
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hC (lane : Nat) (hl : lane < 32) : ∃ j t u o,
      0 < j ∧ j ≤ (X.tr (thread lane)).length ∧ beforeFirstScan X (thread lane) j ∧
      (j = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
      At u 3111 (F lane) ∧
      Run kernel Assumptions.all l (thread lane) {} ((X.tr (thread lane)).take j) (some t) ∧
      Run kernel Assumptions.all l (thread lane) t ((X.tr (thread lane)).drop j) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) t u := by
    obtain ⟨hSame,hLane⟩ := Step.sameWarp_lane hBlock hg hl
    have hEq : warpIndex l g = warpIndex l (thread lane) := hSame.2
    have hw' : warpIndex l (thread lane) < 8 := hEq ▸ hw
    obtain ⟨j,t,u,o,hPos,hBound,hCount,hReady,hAt,hPrefix,hTail,hLocal⟩ :=
      firstShuffleCursorOfMaximal hp hMax hSame.1.2.1 hw' (hProtected _)
    have hWarp : (⟨warpIndex l (thread lane),hw'⟩ : Fin 8) = warp := Fin.ext hEq.symm
    have hLane' : laneOf l (thread lane) = lane := hLane
    have hAt' : At u 3111 (schedulerLane p l (thread lane)
        ⟨warpIndex l (thread lane),hw'⟩
        (if laneOf l (thread lane) ≤ p.batch then p.qOffset (laneOf l (thread lane)) else 0)) := hAt
    exact ⟨j,t,u,o,hPos,hBound,hCount,hReady,
      by
        change At u 3111 (schedulerLane p l (thread lane) warp (schedulerInputWord p lane))
        simpa only [schedulerInputWord,hWarp,hLane'] using hAt',
      hPrefix,hTail,hLocal⟩
  let _ : Inhabited TState := ⟨{}⟩
  choose! j t u o hPos hBound hCount hReady hAt hPrefix hTail hLocal using hC
  exact ⟨o,⟨⟨⟨j,t,u,⟨fun lane hl => (hCount lane hl).1,fun lane hl => (hCount lane hl).2⟩,
    hTail,hLocal,hAt⟩,hPos,hBound,hReady,hPrefix⟩⟩⟩

/-- Every lane of a maximal softmax warp reaches the first-group scan total, with the
decoded inclusive tile prefix in its own live register frame. -/
theorem firstGroupScanOfMaximal (hw : warpIndex l g < 8) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 3150
      (firstUpScanFacts p l g ⟨warpIndex l g,hw⟩ 5) 9 0 ends) := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  obtain ⟨ends,⟨cur⟩⟩ := firstWarpCursor hp hMax hg hw hProtected
  obtain ⟨down⟩ := cur.consumeShuffle (dst := 2683) hp hMax hg .down
    (fun lane => b32 (schedulerInputWord p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ => by simp [schedulerFirstWarpFacts,schedulerLane,schedulerEntry,
      dispatchOutput,dispatchInput])
    (fun lane hl => schedulerFirstShuffleOut hp (cur.checkpoint lane hl))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨first⟩ := down.advanceLocal
    (G := fun lane => firstScanFacts p l (warpLane l g lane) warp) (pc' := 3130) (by
    intro lane hl
    have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
    have hAt := down.checkpoint lane hl
    obtain ⟨_, u, hu, hU⟩ := firstLaneTiles hp
      (show At (down.state lane) 3112
        ((2683, b32 (schedulerInputWord p (shflSource .down
          (laneOf l (warpLane l g lane)) 1 31).1)) :: schedulerLane p l (warpLane l g lane) warp
            (schedulerInputWord p (laneOf l (warpLane l g lane)))) by
        rw [hLane]
        exact hAt)
    exact ⟨u,run_rtg hu,hU⟩)
  exact ⟨ends,warpFirstScanOfMaximal hp hMax hg first⟩

/-- The actual softmax warp's first scheduler decision compares the CTA to the first
group's launch-derived work, after its down shuffle, scan and total broadcast. -/
theorem firstGroupRouteOfMaximal (hw : warpIndex l g < 8) (hProtected : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g
      (if g/l.block < tilePrefix p (min p.batch 31) * p.heads then 3212 else 3155)
      (firstRouteFacts p l g ⟨warpIndex l g,hw⟩) 10 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := firstGroupScanOfMaximal hp hMax hg hw hProtected
  exact ⟨ends,warpFirstRouteOfMaximal hp hMax hg cur⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
