-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderLaterCuQ

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem laterTileGate (l : Launch) (g : Nat) {first lane batch begin finish : Nat}
    (hl : lane < 32) (hi : first + lane < 2 ^ 31) (hb : batch < 2 ^ 31)
    (hBegin : begin < 2 ^ 32) (hFinish : finish < 2 ^ 32) :
    Seg kernel [] l g 4 248
      [(7161, b32 begin), (1728, b32 finish), (1077, b32 (first + lane)), (7170, b32 batch),
       (76, .pred (decide (lane = 31)))] 252
      [(1078, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
       (7162, b32 0), (78, .pred (!decide (first + lane < batch ∧ lane < 31)))] := by
  intro t ht
  have hi32 : first + lane < 2 ^ 32 := by omega
  have hb32 : batch < 2 ^ 32 := by omega
  have hSign {n : Nat} (h : n < 2 ^ 31) :
      toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hBegin (by decide), truncBits_ofNat hFinish (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hi32 (by decide),
        truncBits_ofNat hb32 (by decide), hSign hi, hSign hb, ge_iff_le,
        Int.ofNat_le, Value.pred.injEq]
       by_cases hLane : lane < 31 <;> by_cases hBatch : first + lane < batch <;>
         simp [hLane, hBatch, show lane = 31 ↔ ¬lane < 31 by omega,
           show batch ≤ first + lane ↔ ¬first + lane < batch by omega])

/-- A later group's incoming scan word and the scheduling registers preserved while rounding. -/
def laterTilesFacts (p : Params) (l : Launch) (g warp first : Nat) : List (Nat × Value) :=
  (7162, b32 (groupLaneTiles p first (laneOf l g))) :: laterReadFacts p l g warp first

/-- The decoded later-group arithmetic produces a tile count from its two observed cuQ words
and clips the contribution to zero for the sentinel and out-of-range lanes. -/
theorem loaderLaterTiles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp first : Nat} (hf : first < p.batch) {t : TState}
    (ht : At t 248 ((1728, b32 (drainCuQ p (first + (shflSource .down (laneOf l g) 1 31).1))) ::
      laterReadFacts p l g warp first)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧ At u 263
      (laterTilesFacts p l g warp first) := by
  let lane := laneOf l g
  let active := decide (first + lane < p.batch ∧ lane < 31)
  let begin := drainCuQ p (first + lane)
  let finish := drainCuQ p (first + (shflSource .down lane 1 31).1)
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  let carry := laterReadFacts p l g warp first
  let keep := carry.map Prod.fst
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSize := hp.shape.2.2.2.2.2
  have hi : first + lane < 2 ^ 31 := by omega
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp first lane
  have hCarr : Holds t.regs carry := ht.2.2.2.2.2
  have hAt : At t 248
      [(7161, b32 begin), (1728, b32 finish), (1077, b32 (first + lane)), (7170, b32 p.batch),
       (76, .pred (decide (lane = 31)))] :=
    ht.mono ⟨hCarr.1, ht.2.2.2.2.1, hCarr.2.1, holds_lookup hCarr rfl, hCarr.2.2.1, trivial⟩
  obtain ⟨v, hv, hV⟩ := laterTileGate l g hl hi hp.shape.2.1 hBegin hFinish t hAt
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep := holdsSchedulerFrame hCarr hvFrame (fun _ h => List.mem_map_of_mem h)
  have hBranch : At v 252 ((78, .pred (!active)) :: (1078, .bits 32 diff) ::
      (7162, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_252 (!active) hBranch hBranch.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranch.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  by_cases ha : active = true
  · have hPc : w.pc = 253 := by simpa [ha] using hW.1
    have hRewrite : diff = BitVec.ofNat 64 (finish - begin) := by
      dsimp [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono ha),
        truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
    have hLen : At w 253 [(1078, b32 (finish - begin))] :=
      ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
        by simpa [b32, hRewrite] using hW.2.2.2.2.2.1, trivial⟩
    obtain ⟨u, hu, hU⟩ := loaderLaneTileCount true l g hLength w hLen
    obtain ⟨huA, huFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) hPc
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hu
    have hSaved := holdsSchedulerFrame (show Holds w.regs carry from hW.2.2.2.2.2.2.2)
      huFrame (fun _ h => List.mem_map_of_mem h)
    have hCount : (finish - begin + 255) / 256 = groupLaneTiles p first lane := by
      change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
      rwa [ite_eq_left ha] at hTiles
    have hR := hU.2.2.2.2.1
    change u.regs 7162 = some (b32 ((finish - begin + 255) / 256)) at hR
    rw [hCount] at hR
    exact ⟨15, u, run_comp (run_comp hvA hwA) huA, hU.mono ⟨hR, hSaved⟩⟩
  · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
    have hPc : w.pc = 263 := by simpa [ha'] using hW.1
    have hCount : 0 = groupLaneTiles p first lane := by
      change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
      rwa [ite_eq_right ha] at hTiles
    exact ⟨5, w, run_comp hvA hwA, ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1, by
      change Holds w.regs ((7162, b32 (groupLaneTiles p first lane)) :: carry)
      rw [← hCount]
      exact hW.2.2.2.2.2.2⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
