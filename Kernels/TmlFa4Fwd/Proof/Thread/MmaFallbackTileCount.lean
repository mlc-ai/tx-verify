-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFallbackDown
import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTiles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (localRun)
open PTX.Kernels.TmlFa4Fwd.Softmax (TileRoundSite schedulerRoundUpTiles)

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem fallbackTileGate (l : Launch) (g : Nat) {lane index batch begin finish : Nat}
    (hi : index < 2 ^ 31) (hb : batch < 2 ^ 31)
    (hBegin : begin < 2 ^ 32) (hFinish : finish < 2 ^ 32) (hl : lane < 32) :
    Seg kernel [] l g 4 2002
      [(1184, b32 index), (7203, b32 batch), (7195, b32 begin), (2477, b32 finish),
        (349, .pred (decide (lane = 31)))] 2006
      [(1185, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
        (7196, b32 0), (351, .pred (!decide (index < batch ∧ lane < 31)))] := by
  intro t ht
  have hi32 : index < 2 ^ 32 := by omega
  have hb32 : batch < 2 ^ 32 := by omega
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hBegin (by decide), truncBits_ofNat hFinish (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hb32 (by decide), signedWord hi, signedWord hb, Int.ofNat_le]
       by_cases h : index < batch <;> by_cases hLast : lane < 31 <;>
         simp [h, hLast, show (lane = 31) ↔ ¬ lane < 31 by omega,
           show (batch ≤ index) ↔ ¬ index < batch by omega])

/-- The fallback lane rounds its real pair of neighboring launch offsets to the request tile
count. The last lane and all lanes at or beyond the request limit contribute zero. -/
theorem fallbackLaneTileCount {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first : Nat} {t : TState} (hFirst : first ≤ p.batch)
    (ht : At t 2002 (fallbackNeighborFacts p l g first)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 2017 ((7196, b32 (groupLaneTiles p first (laneOf l g))) ::
        fallbackReadFrame p l g first) := by
  let lane := laneOf l g
  let index := first + lane
  let begin := drainCuQ p index
  let finish := drainCuQ p (first + (shflSource .down lane 1 31).1)
  let active := decide (index < p.batch ∧ lane < 31)
  let F := fallbackReadFrame p l g first
  let length := Value.bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hIndex : index < 2 ^ 31 := by
    have hSize := hp.shape.2.2.2.2.2
    dsimp only [index]
    omega
  obtain ⟨hBegin, hFinish, hMono, hLen, hCount⟩ := drainWordTiles hp first lane
  change begin < 2 ^ 32 at hBegin
  change finish - begin < 2 ^ 30 at hLen
  have input : At t 2002
      [(1184, b32 index), (7203, b32 p.batch), (7195, b32 begin), (2477, b32 finish),
        (349, .pred (decide (lane = 31)))] := by at_select ht
  obtain ⟨v, hv, hV⟩ := fallbackTileGate l g hIndex hp.shape.2.1 hBegin hFinish hLane t input
  have hWriteGate : ((kernel.code.drop 2002).take 4).all
      (fun i => [1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139, 2535, 7502, 7506, 7503].all
        (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
  have hStraightGate : ((kernel.code.drop 2002).take 3).all
      (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
  have hFrameIn : At t 2002 F := ht.mono ht.2.2.2.2.2.2.2.2
  have hSaved := holdsSchedulerFrame hFrameIn.2.2.2.2
    (fun _ hr => schedulerLocalFrame hWriteGate hStraightGate hv ht.1.ge (by rw [ht.1]) hr)
    (fun _ hm => List.mem_map_of_mem hm)
  have hGate : At v 2006 ((351, .pred (!active)) :: (1185, length) :: (7196, b32 0) :: F) :=
    hV.mono ⟨hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hSaved⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2006 (!active) hGate hGate.2.2.2.2.1 (by simp)
  have hRunGate := localRun (pc := 2002) (n := 4) (by decide) (by decide) ht.1 hStraightGate hv
  have hBranch := localRun (pc := 2006) (n := 1) (by decide) (by decide) hGate.1 (by decide) hw
  have hCombined := run_comp hRunGate hBranch
  change (if active then (finish - begin + 255) / 256 else 0) =
    groupLaneTiles p first lane at hCount
  by_cases ha : active = true
  · have hPc : w.pc = 2007 := by simpa [ha] using hW.1
    have hDiff : length = b32 (finish - begin) := by
      dsimp only [length, b32]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono ha),
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hArgs : At w (TileRoundSite.mmaLater.pc)
        [(TileRoundSite.mmaLater.lengthReg, b32 (finish - begin))] :=
      ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, hDiff ▸ hW.2.2.2.2.2.1, trivial⟩
    obtain ⟨u, hu, hU⟩ := schedulerRoundUpTiles .mmaLater l g hLen w hArgs
    have hWriteRound : ((kernel.code.drop 2007).take 10).all
        (fun i => [1183, 7199, 7203, 1182, 1072, 7194, 1180, 7139, 2535, 7502, 7506, 7503].all
          (fun r => !(writesRegs i.op).contains r)) = true := by decide +kernel
    have hStraightRound : ((kernel.code.drop 2007).take 9).all
        (fun i => schedulerFallsThrough i.op) = true := by decide +kernel
    have hKeep := holdsSchedulerFrame hW.2.2.2.2.2.2.2
      (fun _ hr => schedulerLocalFrame hWriteRound hStraightRound hu hPc.ge (by rw [hPc]) hr)
      (fun _ hm => List.mem_map_of_mem hm)
    rw [ite_eq_left ha] at hCount
    exact ⟨15, u, run_comp hCombined
      (localRun (pc := 2007) (n := 10) (by decide) (by decide) hPc hStraightRound hu),
      hU.mono ⟨hCount ▸ hU.2.2.2.2.1, hKeep⟩⟩
  · have hPc : w.pc = 2017 := by simpa [Bool.eq_false_of_not_eq_true ha] using hW.1
    rw [ite_eq_right ha] at hCount
    exact ⟨5, w, hCombined, ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
      hCount ▸ hW.2.2.2.2.2.2⟩⟩

/-- From the recorded fallback offsets, every lane has its exact contribution for the
group's inclusive tile scan. -/
theorem fallbackTileCountOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first count : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (cur : ∀ h, SameWarp l g h → FallbackScanCursor l X h 2000 count
      (fallbackOffsetFacts p l h first)) :
    Nonempty (FallbackScanCursor l X g 2017 (count + 1)
      ((7196, b32 (groupLaneTiles p first (laneOf l g))) :: fallbackReadFrame p l g first)) := by
  obtain ⟨c⟩ := fallbackDownOfMaximal hp hMax hg cur
  obtain ⟨_, u, hu, hU⟩ := fallbackLaneTileCount hp hFirst c.checkpoint
  exact ⟨⟨c.pos, c.before, u, c.lastState, c.pos_pos, c.pos_le, c.shuffleCount, c.ballotCount,
    c.released, hU, c.runPrefix, c.localSteps.trans (run_rtg hu), c.continuation⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
