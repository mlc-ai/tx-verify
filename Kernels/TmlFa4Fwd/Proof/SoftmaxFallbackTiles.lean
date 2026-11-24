-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFallbackWarp
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTiles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem fallbackTileGate (l : Launch) (g : Nat) {lane index batch begin finish : Nat}
    (hi : index < 2 ^ 31) (hb : batch < 2 ^ 31)
    (hBegin : begin < 2 ^ 32) (hFinish : finish < 2 ^ 32) (hl : lane < 32) :
    Seg kernel [] l g 4 3172
      [(1219, b32 index), (7247, b32 batch), (7239, b32 begin), (2704, b32 finish),
        (453, .pred (decide (lane = 31)))] 3176
      [(1220, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
        (7240, b32 0), (455, .pred (!decide (index < batch ∧ lane < 31)))] := by
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

/-- The next group's lane contribution is the rounded difference between its real cuQ words. -/
theorem fallbackLaneTiles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g first cutoff : Nat} {warp : Fin 8} {t : TState} (hGroup : first + 31 < p.batch)
    (ht : At t 3172
      ((2704, b32 (drainCuQ p (first + 31 + (shflSource .down (laneOf l g) 1 31).1))) ::
        fallbackDownFacts p l g warp first cutoff)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 3187 ((7240, b32 (groupLaneTiles p (first + 31) (laneOf l g))) ::
        fallbackAdvanceFacts p l g warp first cutoff) := by
  let lane := laneOf l g
  let start := first + 31
  let index := start + lane
  let begin := drainCuQ p index
  let finish := drainCuQ p (start + (shflSource .down lane 1 31).1)
  let active := decide (index < p.batch ∧ lane < 31)
  let F := fallbackAdvanceFacts p l g warp first cutoff
  let length := Value.bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hIndex : index < 2 ^ 31 := by
    have hSize := hp.shape.2.2.2.2.2
    dsimp only [index, start]
    omega
  obtain ⟨hBegin, hFinish, hMono, hLen, hCount⟩ := drainWordTiles hp start lane
  change begin < 2 ^ 32 at hBegin
  change finish - begin < 2 ^ 30 at hLen
  have hRegs := ht.2.2.2.2
  have hOld : Holds t.regs F := hRegs.2.2.2.2
  have ht' : At t 3172 F := ht.mono hOld
  have htArgs : At t 3172
      [(1219, b32 index), (7247, b32 p.batch), (7239, b32 begin), (2704, b32 finish),
        (453, .pred (decide (lane = 31)))] :=
    ht.mono ⟨hRegs.2.2.2.1, holds_lookup hOld rfl, hRegs.2.2.1, hRegs.1, hRegs.2.1, trivial⟩
  obtain ⟨v, hv, hV⟩ := (fallbackTileGate l g hIndex hp.shape.2.1 hBegin hFinish hLane).apply htArgs
  obtain ⟨hvA, hSaved⟩ := fallbackLinear (by decide) (by decide) ht'
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hGate : At v 3176 ((455, .pred (!active)) :: (1220, length) :: (7240, b32 0) :: F) :=
    hV.mono ⟨hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hSaved⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_3176 (!active) hGate hGate.2.2.2.2.1 (by simp)
  have hwA := Mma.groupScanLocalRun .softmaxSelect (by decide) (by decide) hGate.1 rfl hw
  have hCombined := run_comp hvA hwA
  change (if active then (finish - begin + 255) / 256 else 0) =
    groupLaneTiles p start lane at hCount
  by_cases ha : active = true
  · have hwPc : w.pc = 3177 := by simpa [ha] using hW.1
    have hNat := hMono ha
    have hDiff : length = b32 (finish - begin) := by
      dsimp only [length, b32]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) hNat,
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hwArgs : At w (TileRoundSite.later.pc)
        [(TileRoundSite.later.lengthReg, b32 (finish - begin))] :=
      ⟨hwPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, hDiff ▸ hW.2.2.2.2.2.1, trivial⟩
    obtain ⟨u, hu, hU⟩ := (schedulerRoundUpTiles .later l g hLen).apply hwArgs
    have hwFrame : At w 3177 F := ⟨hwPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.2.2.2⟩
    obtain ⟨huA, hFrame⟩ := fallbackLinear (by decide) (by decide) hwFrame
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    rw [ite_eq_left ha] at hCount
    exact ⟨15, u, run_comp hCombined huA, hU.mono ⟨hCount ▸ hU.2.2.2.2.1, hFrame⟩⟩
  · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
    have hwPc : w.pc = 3187 := by simpa [ha'] using hW.1
    rw [ite_eq_right ha] at hCount
    exact ⟨5, w, hCombined, ⟨hwPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
      hCount ▸ hW.2.2.2.2.2.2⟩⟩

/-- Every lane obtains its next request's tile count from the adjacent protected offsets. -/
theorem warpFallbackTilesPreserving {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first cutoff shuffles votes : Nat} {warp : Fin 8}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3172 (fun lane =>
      (2704, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        fallbackDownFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3187 (fun lane =>
        (7240, b32 (groupLaneTiles p (first + 31) (laneOf l (warpLane l g lane)))) ::
          fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends,
      u.pos = cur.pos ∧ u.before = cur.before := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  apply cur.advanceLocalPreserving
  intro lane hl
  have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hAt := cur.checkpoint lane hl
  have hAt' : At (cur.state lane) 3172
      ((2704, b32 (drainCuQ p (first + 31 +
        (shflSource .down (laneOf l (warpLane l g lane)) 1 31).1))) ::
        fallbackDownFacts p l (warpLane l g lane) warp first cutoff) := by
    rw [hLane]
    exact hAt
  obtain ⟨_, u, hu, hU⟩ := fallbackLaneTiles hp hGroup hAt'
  exact ⟨u, run_rtg hu, hU⟩

theorem warpFallbackTiles {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g first cutoff shuffles votes : Nat} {warp : Fin 8}
    (hg : g < l.threads) (hGroup : first + 31 < p.batch) {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 3172 (fun lane =>
      (2704, b32 (drainCuQ p (first + 31 + (shflSource .down lane 1 31).1))) ::
        fallbackDownFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends) :
    ∃ u : SchedulerWarpAt l X g 3187 (fun lane =>
        (7240, b32 (groupLaneTiles p (first + 31) (laneOf l (warpLane l g lane)))) ::
          fallbackAdvanceFacts p l (warpLane l g lane) warp first cutoff) shuffles votes ends,
      u.pos = cur.pos := by
  obtain ⟨u, hPos, _⟩ := warpFallbackTilesPreserving hp hg hGroup cur
  exact ⟨u, hPos⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
