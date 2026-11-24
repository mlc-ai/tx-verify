-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSchedulerProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderFirstScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

private theorem seedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 206
      (loaderScanFacts p l g (warpIndex l g) 0) 4 0 ends) := by
  obtain ⟨ends,⟨cur⟩⟩ := firstShuffleOfMaximal hp hMax hg hw hCuQ
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨down⟩ := cur.consumeShuffle (dst := 1707) hp hMax hg .down
    (fun lane => b32 (drainCuQ p lane)) (fun _ => 1) (fun _ => 31)
    (fun _ _ _ hm heq => by
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [heq] at hMem
      exact (of_decide_eq_true rfl : 1707 ∉
        [7159,1073,7170,1072,1062,2535,1,7492,7493,7494,7495,1663,1664,7496,7497,7498,7499,7500,
          7501,7502,7503,7504,7505,7291,7290,7289,7506,7292,7293,7294,7295,1665,1061]) hMem)
    (fun lane hl => by
      simpa only [hLane lane hl] using loaderDownTemplate hp (cur.checkpoint lane hl))
  refine ⟨ends,down.advanceLocal ?_⟩
  intro lane hl
  have hAt := down.checkpoint lane hl
  have hAt' : At (down.state lane) 188
      ((1707,b32 (drainCuQ p (shflSource .down (laneOf l (warpLane l g lane)) 1 31).1)) ::
        loaderCuQFacts p l (warpLane l g lane) (warpIndex l g)) := by
    rw [hLane lane hl]
    exact hAt
  obtain ⟨_,u,hu,hU⟩ := loaderFirstTiles hp hAt'
  have hReg := hU.2.2.2.2.1
  rw [hLane lane hl] at hReg
  refine ⟨u,run_rtg hu,hU.mono ⟨?_,hU.2.2.2.2⟩⟩
  change u.regs 7162 = some (b32 (prefixWindow (groupLaneTiles p 0) 1 lane))
  simpa only [prefixWindow_one] using hReg

private theorem scanRound {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g warp shuffles : Nat} (hg : g < l.threads) (stage : Fin 5)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (loaderScanPc stage)
      (loaderScanFacts p l g warp stage.val) shuffles 0 ends) :
    Nonempty (SchedulerWarpReached l X g (loaderScanPc stage + 4)
      (loaderScanFacts p l g warp (stage.val + 1)) (shuffles + 1) 0 ends) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨read⟩ := cur.consumeShuffle hp hMax hg .up
    (fun lane => b32 (prefixWindow (groupLaneTiles p 0) (2 ^ stage.val) lane))
    (fun _ => 2 ^ stage.val) (fun _ => 0) (fun _ _ _ => loaderScanDstFresh stage)
    (fun lane hl => loaderFirstScanOut hp stage (cur.checkpoint lane hl))
  exact read.advanceLocal
    (fun lane hl => loaderFirstScanFoldLocal hp stage hl (Step.sameWarp_lane hBlock hg hl).2
      (read.checkpoint lane hl))

/-- The loader reaches the actual first-group decision in a maximal execution. -/
theorem firstRouteOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g
      (if g / l.block < tilePrefix p (min p.batch 31) * p.heads then 288 else 231)
      (loaderFirstRouteFacts p l g (warpIndex l g)) 10 0 ends) := by
  obtain ⟨ends,⟨s0⟩⟩ := seedOfMaximal hp hMax hg hw hCuQ
  obtain ⟨s1⟩ := scanRound hp hMax hg 0 s0
  obtain ⟨s2⟩ := scanRound hp hMax hg 1 s1
  obtain ⟨s3⟩ := scanRound hp hMax hg 2 s2
  obtain ⟨s4⟩ := scanRound hp hMax hg 3 s3
  obtain ⟨s5⟩ := scanRound hp hMax hg 4 s4
  let part := prefixWindow (groupLaneTiles p 0) 32
  obtain ⟨total⟩ := s5.consumeShuffle (dst := 7164) hp hMax hg .idx
    (fun lane => b32 (part lane)) (fun _ => 31) (fun _ => 31)
    (fun _ _ _ hm heq => by
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [heq] at hMem
      exact (of_decide_eq_true rfl : 7164 ∉
        (loaderScanFacts p l g (warpIndex l g) 5 _).map Prod.fst) hMem)
    (fun lane hl => by
      have ht := s5.checkpoint lane hl
      refine (loaderOutCore (by rw [ht.1]; decide) (by rw [ht.1]; decide)).trans ?_
      exact loaderFirstTotalTemplate hp _ _ _ ht.1 ht.2.2.2.1 ht.2.2.2.2.1)
  exact ⟨ends,total.advanceLocal (fun lane hl => loaderFirstRouteLocal hp hg hl
    (total.checkpoint lane hl))⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
