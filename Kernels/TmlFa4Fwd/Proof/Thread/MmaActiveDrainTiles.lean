-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainStart
import all Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTiles
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Thread.Allocation (drainRoots signedWord)

/-- Shared rounded division for either generated terminal scan group. -/
theorem activeDrainRoundUpTiles (later : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (if later then 2715 else 2658)
      [((if later then 1199 else 1195), b32 len)] (if later then 2725 else 2668)
      [(7212, b32 ((len + 255) / 256))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h31 : len < 2 ^ 31 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 256 < 2 ^ 32 := by omega
  have hMask : len / 256 * 256 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr8 : (len : Int) / 2 ^ 8 = (len / 256 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s8 : min (truncBits 32 (BitVec.ofInt 64 8)).toNat 32 = 8 := rfl
  have s24 : (truncBits 32 (BitVec.ofInt 64 24)).toNat = 24 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 24 = 0 := rfl
  have h24 : ¬24 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-256)) = BitVec.ofNat 64 4294967040 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel [] l g 8 (if later then 2715 else 2658)
      [((if later then 1199 else 1195), b32 len)] (if later then 2723 else 2666)
      [((if later then 2658 else 2637), b32 (len / 256)),
       ((if later then 427 else 413), .pred (decide (len ≠ len / 256 * 256)))] := by
    cases later <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s8, s24, ite_eq_right h24, shr31, shr8, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, signedWord h31, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowByteMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 256 * 256 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 (if later then 2723 else 2666)
      [((if later then 2658 else 2637), b32 (len / 256)),
       ((if later then 427 else 413), .pred (decide (len ≠ len / 256 * 256)))]
      (if later then 2725 else 2668)
      [(7212, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      cases later <;> intro t ht <;> simp only [hPad] at ht <;>
        seg_fp ht using norm_bits
    · cases later <;> intro t ht <;> simp only [decide_eq_true h] at ht <;>
        seg_fp ht using norm_bits
  exact hFirst.comp hLast

/-- Turn a straight local replay into an all-assumptions path, retaining its caller frame. -/
theorem activeDrainLocalKeep {l : Launch} {g pc n : Nat} {s t : TState}
    {F : List (Nat × Value)} (hs : At s pc F) (hLo : 1904 ≤ pc) (hHi : pc+n ≤ 2768)
    (hKeep : ((kernel.code.drop pc).take n).all
      (fun i => (F.map Prod.fst).all fun r => !(writesRegs i.op).contains r) = true)
    (hStraight : ((kernel.code.drop pc).take (n-1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n s = some t) :
    Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧ Holds t.regs F := by
  exact ⟨run_rtg (localRun hLo hHi hs.1 hStraight hr),holdsSchedulerFrame hs.2.2.2.2
    (fun _ hm => schedulerLocalFrame hKeep hStraight hr hs.1.ge (by rw [hs.1]) hm)
    (fun _ hm => List.mem_map_of_mem hm)⟩

/-- The decoded operands shared by the first and recurring terminal groups. -/
def activeDrainCommon (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  (7149,b32 p.batch)::(7139,b32 p.heads)::drainRoots p l g

/-- The first drain group rounds the actual protected CuQ differences. -/
theorem ActiveDrainNeighbors.tiles {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) (c : ActiveDrainNeighbors p l X g) :
    Nonempty (SchedulerWarpReached l X g 2668 (fun i => let th := warpLane l g i
        (7212,b32 (groupLaneTiles p 0 (laneOf l th)))::activeDrainCommon p l th)
      c.shuffles c.votes c.ends) := by
  apply c.reached.advanceLocal
  intro i hi
  let th := warpLane l g i
  let lane := laneOf l th
  let left := drainCuQ p lane
  let right := drainCuQ p (shflSource .down lane 1 31).1
  let guard := !decide (laneHasRequest lane p.batch)
  let diff := truncBits 32 (BitVec.ofNat 64 right - BitVec.ofNat 64 left)
  let F := activeDrainCommon p l th
  have hBlock : l.block %32 = 0 := by rw [hp.block]
  have hLane : lane = i := (Step.sameWarp_lane hBlock hg hi).2
  have hPeer : laneOf l (warpLane l g (shflSource .down i 1 31).1) =
      (shflSource .down i 1 31).1 := (Step.sameWarp_lane hBlock hg
    (Step.shflSource_lt .down hi (1 : Nat) (31 : Nat))).2
  obtain ⟨hLeft,hRight,hMono,hLength,hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hLeft hRight hMono hLength hTiles
  change left < 2^32 at hLeft
  change right < 2^32 at hRight
  have h := c.reached.checkpoint i hi
  have hAt : At (c.reached.state i) 2655
      ([(2633,b32 right),(7209,b32 left),(337,.pred guard)] ++ F) := by
    apply h.mono
    refine ⟨?_,h.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2⟩
    simpa only [right,lane,hLane,hPeer] using h.2.2.2.2.1
  have hd : Seg kernel [] l th 2 2655 [(2633,b32 right),(7209,b32 left)] 2657
      [(1195,.bits 32 diff),(7212,b32 0)] := by
    intro s hs
    seg_fp hs using
      first
      | rfl
      | simp only [diff,truncBits_ofNat hLeft (by decide),truncBits_ofNat hRight (by decide)]
  obtain ⟨u,hu,hU⟩ := hd.apply (hAt.mono ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.1,trivial⟩)
  have hSaved : At (c.reached.state i) 2655 ((337,.pred guard)::F) :=
    hAt.mono hAt.2.2.2.2.2.2
  obtain ⟨hPath,hPreserve⟩ := activeDrainLocalKeep hSaved (by decide) (by decide)
    (by
      change ((kernel.code.drop 2655).take 2).all
        (fun i => [337,7149,7139,1180,7506,1072].all
          (fun r => !(writesRegs i.op).contains r)) = true
      decide +kernel)
    (by decide +kernel) hu
  have hFrame : At u 2657 ([(1195,.bits 32 diff),(7212,b32 0),(337,.pred guard)] ++ F) :=
    hU.mono ⟨hU.2.2.2.2.1,hU.2.2.2.2.2.1,hPreserve⟩
  obtain ⟨v,hv,hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := th)
    Flow.code_2657 guard hFrame hPreserve.1 (by simp)
  have hSteps := hPath.trans (run_rtg (localRun (by decide) (by decide) hFrame.1 rfl hv))
  by_cases ha : laneHasRequest lane p.batch
  · have hPc : v.pc = 2658 := by simpa [guard,ha] using hV.1
    have hDiff : diff = BitVec.ofNat 64 (right-left) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show left < 2^64 by omega) (hMono (decide_eq_true ha)),
        truncBits_ofNat (show right-left < 2^32 by omega) (by decide)]
    have hLen : At v 2658 [(1195,b32 (right-left))] :=
      ⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,by
        simpa only [b32,hDiff] using hV.2.2.2.2.1,trivial⟩
    obtain ⟨w,hw,hW⟩ := (activeDrainRoundUpTiles false l th hLength).apply hLen
    have hCarry := hLen.mono (show Holds v.regs F from hV.2.2.2.2.2.2.2)
    obtain ⟨hMore,hF⟩ := activeDrainLocalKeep hCarry (by decide) (by decide)
      (by
        change ((kernel.code.drop 2658).take 10).all
          (fun i => [7149,7139,1180,7506,1072].all
            (fun r => !(writesRegs i.op).contains r)) = true
        decide +kernel)
      (by decide +kernel) hw
    rw [decide_eq_true ha] at hTiles
    refine ⟨w,hSteps.trans hMore,hW.mono ⟨?_,hF⟩⟩
    rw [← hTiles]
    exact hW.2.2.2.2.1
  · have hPc : v.pc = 2668 := by simpa [guard,ha] using hV.1
    rw [decide_eq_false ha] at hTiles
    refine ⟨v,hSteps,⟨hPc,hV.2.1,hV.2.2.1,hV.2.2.2.1,?_,hV.2.2.2.2.2.2.2⟩⟩
    rw [← hTiles]
    exact hV.2.2.2.2.2.1

end PTX.Kernels.TmlFa4Fwd.Mma
