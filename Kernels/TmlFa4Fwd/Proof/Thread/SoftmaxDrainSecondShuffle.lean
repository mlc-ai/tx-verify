-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalFirstShuffle
import all Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTiles
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Shared rounded division for either generated terminal scan group. -/
theorem drainRoundUpTiles (later : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (if later then 7685 else 7626)
      [((if later then 1610 else 1605), b32 len)] (if later then 7695 else 7636)
      [(7262, b32 ((len + 255) / 256))] := by
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
  have hFirst : Seg kernel [] l g 8 (if later then 7685 else 7626)
      [((if later then 1610 else 1605), b32 len)] (if later then 7693 else 7634)
      [((if later then 5840 else 5819), b32 (len / 256)),
       ((if later then 670 else 656), .pred (decide (len ≠ len / 256 * 256)))] := by
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
  have hLast : Seg kernel [] l g 2 (if later then 7693 else 7634)
      [((if later then 5840 else 5819), b32 (len / 256)),
       ((if later then 670 else 656), .pred (decide (len ≠ len / 256 * 256)))]
      (if later then 7695 else 7636)
      [(7262, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      cases later <;> intro t ht <;> simp only [hPad] at ht <;>
        seg_fp ht using norm_bits
    · cases later <;> intro t ht <;> simp only [decide_eq_true h] at ht <;>
        seg_fp ht using norm_bits
  exact hFirst.comp hLast

/-- Exact word at the next full-warp scheduler scan. -/
def terminalSecondScanFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7262,b32 (groupLaneTiles p 0 (laneOf l g))),(7141,b32 p.heads),
    (657,.pred (decide (15 < laneOf l g))),(658,.pred (decide (7 < laneOf l g))),
    (659,.pred (decide (3 < laneOf l g))),(660,.pred (decide (1 < laneOf l g))),
    (661,.pred (decide (laneOf l g = 0)))] ++ RowDrainRole.softmax.roots p l g

private theorem drainHeadsParameter {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} {F : List (Nat × Value)}
    (ht : At t 7636 F) (hFresh : ∀ pair ∈ F, pair.1 ≠ 7141) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7637 ((7141,b32 p.heads)::F) := by
  obtain ⟨hBits,hParam⟩ := hp.values (17,p.heads) (by simp [Params.scalarWords])
  have hName : param 17 =
      "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_object_at__ten\
      sor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16gmemalign16o1i64\
      div8_0_param_17" := by
    have hDec : toString (17 : Nat) = "17" := by
      rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
      simp only [show (17 / 10 : Nat) = 1 by decide, show (17 % 10 : Nat) = 7 by decide,
        Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 7) (by decide),
        Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_seven.mpr rfl]
      rfl
    unfold param
    rw [hDec]
    set_option maxRecDepth 2000 in rfl
  have hCode : kernel.code[7636]? = some ⟨none,.mem
      {kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
        addr := ⟨.param (param 17) false,0⟩, dsts := [some 7141]}⟩ := by
    rw [hName]
    exact Flow.code_7636
  have hr := Loader.scalarLoad (g := g) ht hParam hBits hCode
  exact ⟨_,RowDrainRole.softmax.drainLocals (by decide) (by decide) ht.1 (by simp) hr,
    ht.set hFresh⟩

private theorem drainScanPredicates {p : Params} {l : Launch}
    {g : Nat} {t : TState} (ht : At t 7637
      ((7141,b32 p.heads)::(7262,b32 (groupLaneTiles p 0 (laneOf l g)))::
        RowDrainRole.softmax.roots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 7642 (terminalSecondScanFrame p l g) := by
  have hLane32 : laneOf l g < 2^32 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  have hLane64 : laneOf l g < 2^64 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  let F : List (Nat × Value) :=
    [(657,.pred (decide (15 < laneOf l g))),(658,.pred (decide (7 < laneOf l g))),
    (659,.pred (decide (3 < laneOf l g))),(660,.pred (decide (1 < laneOf l g))),
    (661,.pred (decide (laneOf l g = 0)))]
  have hLocal : ∃ u, run kernel [] l g 5 t = some u ∧ At u 7642 F := by
    have ht' : At t 7637 [(1215,b32 (laneOf l g))] := by
      exact ht.mono ⟨ht.2.2.2.2.2.2.2.1,trivial⟩
    dsimp only [F]
    seg_fp ht' using
      simp [compare,truncBits_ofNat hLane32 (by decide),toNat_ofNat_lt hLane64,
        show (truncBits 32 15#64).toNat = 15 by decide,
        show (truncBits 32 7#64).toNat = 7 by decide,
        show (truncBits 32 3#64).toNat = 3 by decide,
        show (truncBits 32 1#64).toNat = 1 by decide,
        show (truncBits 32 0#64).toNat = 0 by decide]
  obtain ⟨u,hr,hu⟩ := hLocal
  have hKeep : Holds u.regs
      ((7141,b32 p.heads)::(7262,b32 (groupLaneTiles p 0 (laneOf l g)))::
        RowDrainRole.softmax.roots p l g) := by
    apply holdsSchedulerFrame ht.2.2.2.2
      (regs := [7141,7262,1215,7506,1072,7151])
    · intro r hR
      exact schedulerLocalFrame (lo := 7637) (len := 5)
        (by decide +kernel) (by decide +kernel) hr ht.1.ge (by rw [ht.1]) hR
    · intro item hm
      simp only [RowDrainRole.roots,RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,
        RowDrainRole.ctaReg,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact ⟨u,RowDrainRole.softmax.drainLocals (by decide) (by decide) ht.1 (by decide +kernel) hr,
    hu.mono ⟨hKeep.2.1,hKeep.1,hu.2.2.2.2.1,hu.2.2.2.2.2.1,hu.2.2.2.2.2.2.1,
      hu.2.2.2.2.2.2.2.1,hu.2.2.2.2.2.2.2.2.1,hKeep.2.2⟩⟩

/-- The scheduler predicate initialized before the first group is reused during drainage. -/
def terminalRequestGuard (p : Params) (l : Launch) (g : Nat) : Bool :=
  !decide (laneHasRequest (laneOf l g) p.batch)

private theorem terminalDrainCounts {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (ht : At t 7623
      [(5815,b32 (drainCuQ p (shflSource .down (laneOf l g) 1 31).1)),
       (7259,b32 (drainCuQ p (laneOf l g))),(441,.pred (terminalRequestGuard p l g))]) :
    ∃ u n, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      run kernel [] l g 2 t = some n ∧ n.pc = 7625 ∧
      (∃ w, run kernel [] l g 1 n = some w ∧
        (w = u ∨ w.pc = 7626 ∧ run kernel [] l g 10 w = some u)) ∧
      At u 7636 [(7262,b32 (groupLaneTiles p 0 (laneOf l g)))] := by
  let lane := laneOf l g
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  let active := decide (laneHasRequest lane p.batch)
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  obtain ⟨hBegin,hFinish,hMono,hLength,hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  have hInitial : ∃ n, run kernel [] l g 2 t = some n ∧
      At n 7625 [(1605,.bits 32 diff),(7262,b32 0),(441,.pred (!active))] := by
    dsimp only [diff,finish,begin,lane,active] at *
    seg_fp ht using
      first
      | rfl
      | simp only [truncBits_ofNat hBegin (by decide),truncBits_ofNat hFinish (by decide)]
  obtain ⟨n,hn,hN⟩ := hInitial
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7625 (!active) hN hN.2.2.2.2.2.2.1 (by simp)
  have hLocal := (RowDrainRole.softmax.drainLocals (n := 2) (by decide) (by decide)
    ht.1 (by decide +kernel) hn).trans
    (RowDrainRole.softmax.drainLocals (n := 1) (by decide) (by decide) hN.1 (by simp) hw)
  by_cases ha : active = true
  · have hPc : w.pc = 7626 := by simpa [ha] using hW.1
    have hDiff : diff = BitVec.ofNat 64 (finish-begin) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2^64 by omega) (hMono ha),
        truncBits_ofNat (show finish-begin < 2^32 by omega) (by decide)]
    have hLen : At w 7626 [(1605,b32 (finish-begin))] :=
      ⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,
        by simpa [b32,hDiff] using hW.2.2.2.2.1,trivial⟩
    obtain ⟨u,hu,hU⟩ := drainRoundUpTiles false l g hLength w hLen
    have hCount : (finish-begin+255)/256 = groupLaneTiles p 0 lane := by
      change (if active then (finish-begin+255)/256 else 0) = _ at hTiles
      rwa [ite_eq_left ha] at hTiles
    exact ⟨u,n,hLocal.trans (RowDrainRole.softmax.drainLocals (by decide) (by decide)
      hPc (by decide +kernel) hu),hn,hN.1,⟨w,hw,.inr ⟨hPc,hu⟩⟩,by
      change At u 7636 [(7262,b32 (groupLaneTiles p 0 lane))]
      rw [← hCount]
      exact hU⟩
  · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
    have hPc : w.pc = 7636 := by simpa [ha'] using hW.1
    have hCount : 0 = groupLaneTiles p 0 lane := by
      change (if active then (finish-begin+255)/256 else 0) = _ at hTiles
      rwa [ite_eq_right ha] at hTiles
    exact ⟨w,n,hLocal,hn,hN.1,⟨w,hw,.inl rfl⟩,⟨hPc,hW.2.1,hW.2.2.1,hW.2.2.2.1,
      by
        change w.regs 7262 = some (b32 (groupLaneTiles p 0 lane))
        rw [← hCount]
        exact hW.2.2.2.2.2.1,trivial⟩⟩

private theorem firstEndpoint_eq_drain (p : Params) (l : Launch) (g : Nat) :
    terminalFirstWord p l g = drainCuQ p (laneOf l g) := rfl

/-- Advance the actual warp from completed down-shuffle to the first up-shuffle of the drain. -/
theorem terminalDrainSecondShuffleOfWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7623
      (fun lane => let t := warpLane l g lane
        let peer := warpLane l g (shflSource .down lane 1 31).1
        (5815,b32 (terminalFirstWord p l peer)) ::
          (7259,b32 (terminalFirstWord p l t)) :: RowDrainRole.softmax.roots p l t)
      shuffles votes ends)
    (hGuard : ∀ lane < 32, (cur.state lane).regs 441 =
      some (.pred (terminalRequestGuard p l (warpLane l g lane)))) :
    Nonempty (SchedulerWarpReached l X g 7642
      (fun lane => terminalSecondScanFrame p l (warpLane l g lane)) shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let thread := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hPeer : laneOf l (warpLane l g (shflSource .down lane 1 31).1) =
      (shflSource .down lane 1 31).1 := by
    apply (Step.sameWarp_lane hBlock hg ?_).2
    exact Step.shflSource_lt .down hl 1 31
  have ht := cur.checkpoint lane hl
  have hAt : At (cur.state lane) 7623
      [(5815,b32 (drainCuQ p (shflSource .down (laneOf l thread) 1 31).1)),
       (7259,b32 (drainCuQ p (laneOf l thread))),
       (441,.pred (terminalRequestGuard p l thread))] := by
    apply ht.mono
    refine ⟨?_,?_,hGuard lane hl,trivial⟩
    · simpa only [firstEndpoint_eq_drain,hPeer,hLane] using ht.2.2.2.2.1
    · simpa only [firstEndpoint_eq_drain] using ht.2.2.2.2.2.1
  obtain ⟨u,n,hPath,hn,hN,⟨w,hw,hTail⟩,hAtU⟩ := terminalDrainCounts hp hAt
  let regs := [1215,7506,1072,7151]
  have hKeep (r : Nat) (hr : r ∈ regs) :
      u.regs r = (cur.state lane).regs r := by
    have hA := schedulerLocalFrame (lo := 7623) (len := 2)
      (by decide +kernel : ((kernel.code.drop 7623).take 2).all
        (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
      (by decide +kernel) hn ht.1.ge (by rw [ht.1]) hr
    have hB := schedulerLocalFrame (lo := 7625) (len := 1)
      (by decide +kernel : ((kernel.code.drop 7625).take 1).all
        (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
      (by decide +kernel) hw hN.ge (by rw [hN]) hr
    rcases hTail with rfl | ⟨hW,hu⟩
    · exact hB.trans hA
    · have hC := schedulerLocalFrame (lo := 7626) (len := 10)
        (by decide +kernel : ((kernel.code.drop 7626).take 10).all
          (fun ins => regs.all (fun r => !(writesRegs ins.op).contains r)) = true)
        (by decide +kernel) hu hW.ge (by rw [hW]) hr
      exact hC.trans (hB.trans hA)
  have hRoots : Holds u.regs (RowDrainRole.softmax.roots p l thread) := by
    apply holdsSchedulerFrame ht.2.2.2.2.2.2 hKeep
    intro item hm
    simp only [RowDrainRole.roots,RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,
      RowDrainRole.ctaReg,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [regs]
  have hAtU' : At u 7636 ((7262,b32 (groupLaneTiles p 0 (laneOf l thread)))::
      RowDrainRole.softmax.roots p l thread) := hAtU.mono ⟨hAtU.2.2.2.2.1,hRoots⟩
  obtain ⟨v,hV,hAtV⟩ := drainHeadsParameter hp hAtU' (by
    simp [RowDrainRole.roots,RowDrainRole.batchReg,RowDrainRole.frame,RowDrainRole.laneReg,
      RowDrainRole.ctaReg])
  obtain ⟨z,hZ,hAtZ⟩ := drainScanPredicates hAtV
  exact ⟨z,hPath.trans (hV.trans hZ),hAtZ⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
