-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitPublished
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import all Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Flow.Code.Part028

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader (loaderLinear)

/-- Shared rounded division for either generated terminal scan group. -/
theorem cacheDrainRoundUpTiles (later : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (if later then 1813 else 1755)
      [((if later then 1176 else 1172), b32 len)] (if later then 1823 else 1765)
      [(7187, b32 ((len + 255) / 256))] := by
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
  have hFirst : Seg kernel [] l g 8 (if later then 1813 else 1755)
      [((if later then 1176 else 1172), b32 len)] (if later then 1821 else 1763)
      [((if later then 2264 else 2243), b32 (len / 256)),
       ((if later then 248 else 234), .pred (decide (len ≠ len / 256 * 256)))] := by
    cases later <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s8, s24, ite_eq_right h24, shr31, shr8, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, RowDrainRole.signedWord h31, hNeg, gt_iff_lt, hPos, decide_true,
        Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowByteMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 256 * 256 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 (if later then 1821 else 1763)
      [((if later then 2264 else 2243), b32 (len / 256)),
       ((if later then 248 else 234), .pred (decide (len ≠ len / 256 * 256)))]
      (if later then 1823 else 1765)
      [(7187, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      cases later <;> intro t ht <;> simp only [hPad] at ht <;>
        seg_fp ht using norm_bits
    · cases later <;> intro t ht <;> simp only [decide_eq_true h] at ht <;>
        seg_fp ht using norm_bits
  exact hFirst.comp hLast

def firstGroupCarry (p : Params) (l : Launch) (g use : Nat) : List (Nat × Value) :=
  (7145,b32 p.batch)::firstDrainTail p l g use

private theorem firstGroupCountLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {t : TState}
    (ht : At t 1752 ([(2239,b32 (drainCuQ p (shflSource .down (laneOf l g) 1 31).1)),
        (7184,b32 (drainCuQ p (laneOf l g)))] ++ firstGroupCarry p l g use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1765 ((7187,b32 (groupLaneTiles p 0 (laneOf l g)))::firstGroupCarry p l g use) := by
  let lane := laneOf l g
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  let active := decide (laneHasRequest lane p.batch)
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  let F := firstGroupCarry p l g use
  obtain ⟨ha,hb,hMono,hLength,hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at ha hb hMono hLength hTiles
  have hCalc : Seg kernel [] l g 2 1752 [(2239,b32 finish),(7184,b32 begin)] 1754
      [(1172,.bits 32 diff),(7187,b32 0)] := by
    intro s hs
    dsimp only [diff,begin,finish,lane] at *
    seg_fp hs using
      first
      | rfl
      | simp only [truncBits_ofNat ha (by decide),truncBits_ofNat hb (by decide)]
  obtain ⟨v,hCalc,hV⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hCalc ht
  have hGuard : (64,.pred (!active)) ∈ F := by
    simp [F,firstGroupCarry,firstDrainTail,drainSchedulerFrame,active,lane]
  have hv : At v 1754 ((64,.pred (!active)) :: (1172,.bits 32 diff) :: (7187,b32 0) :: F) :=
    hV.mono ⟨holds_mem hV.2.2.2.2 (List.mem_append_right _ hGuard),hV.2.2.2.2⟩
  obtain ⟨w,hBranch,hw⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1754 (!active) hv hv.2.2.2.2.1 (by simp)
  have hBranchAll := (loaderLinear (regs := []) (by decide) (by decide) hv.1
    (by simp) (by decide) hBranch).1
  have hSteps := (run_rtg hCalc).trans (run_rtg hBranchAll)
  change (if active then (finish-begin+255)/256 else 0) = groupLaneTiles p 0 lane at hTiles
  by_cases hActive : active = true
  · have hPc : w.pc = 1755 := by simpa [hActive] using hw.1
    have hDiff : diff = BitVec.ofNat 64 (finish-begin) := by
      dsimp only [diff]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2^64 by omega) (hMono hActive),
        truncBits_ofNat (show finish-begin < 2^32 by omega) (by decide)]
    have hAt : At w 1755 ([(1172,b32 (finish-begin))]++F) :=
      ⟨hPc,hw.2.1,hw.2.2.1,hw.2.2.2.1,by
        have hReg := hw.2.2.2.2.2.1
        rw [hDiff] at hReg
        exact ⟨hReg,hw.2.2.2.2.2.2.2⟩⟩
    obtain ⟨u,hRun,hU⟩ := linearFramed (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (cacheDrainRoundUpTiles false l g hLength) hAt
    have hCount : (finish-begin+255)/256 = groupLaneTiles p 0 lane := by
      rwa [ite_eq_left hActive] at hTiles
    exact ⟨u,hSteps.trans (run_rtg hRun),by rw [← hCount]; exact hU⟩
  · have hPc : w.pc = 1765 := by simpa [Bool.eq_false_of_not_eq_true hActive] using hw.1
    have hCount : 0 = groupLaneTiles p 0 lane := by rwa [ite_eq_right hActive] at hTiles
    exact ⟨w,hSteps,⟨hPc,hw.2.1,hw.2.2.1,hw.2.2.2.1,by
      rw [← hCount]
      exact hw.2.2.2.2.2.2⟩⟩

/-- Guard bits carried by either of the loader's terminal prefix scans. -/
def cacheDrainScanGuard (stage : Fin 5) (lane : Nat) : Bool :=
  if stage.val = 0 then decide (lane = 0) else decide (2^stage.val ≤ lane)

/-- The first and subsequent scans use separate predicate registers. -/
def cacheDrainGuardReg (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 253 else 239)-stage.val

def cacheDrainGuardFrame (later : Bool) (lane : Nat) : List (Nat × Value) :=
  (List.finRange 5).map fun stage =>
    (cacheDrainGuardReg later stage,.pred (cacheDrainScanGuard stage lane))

/-- The first actual terminal group is ready to scan all five prefix offsets. -/
def firstGroupScanFrame (p : Params) (l : Launch) (g use : Nat) : List (Nat × Value) :=
  (7187,b32 (groupLaneTiles p 0 (laneOf l g))) :: cacheDrainGuardFrame false (laneOf l g) ++
    (7137,b32 p.heads) :: firstGroupCarry p l g use

private theorem prepareFirstGroupScan {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g use : Nat} {t : TState}
    (ht : At t 1765 ((7187,b32 (groupLaneTiles p 0 (laneOf l g)))::firstGroupCarry p l g use)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 1771 (firstGroupScanFrame p l g use) := by
  let lane := laneOf l g
  let F := (7187,b32 (groupLaneTiles p 0 lane))::firstGroupCarry p l g use
  let v := next (setReg t 7137 (b32 p.heads))
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
  have hLoad : run kernel [] l g 1 t = some v :=
    Loader.scalarLoad ht hParam hBits (by rw [hName]; exact Flow.code_1765)
  have hLoadAll := (loaderLinear (regs := []) (by decide) (by decide) ht.1
    (by simp) (by decide) hLoad).1
  have hv : At v 1766 ((7137,b32 p.heads)::F) := ht.set (by
    simp [firstGroupCarry,firstDrainTail,drainCarry,drainSchedulerFrame])
  have hL32 : lane < 2^32 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  have hL64 : lane < 2^64 := (Nat.mod_lt _ (by decide : 0 < 32)).trans (by decide)
  have hGuard : Seg kernel [] l g 5 1766 [(1073,b32 lane)] 1771
      (cacheDrainGuardFrame false lane) := by
    intro s hs
    change ∃ w, run kernel [] l g 5 s = some w ∧ At w 1771
      [(239,.pred (decide (lane = 0))),(238,.pred (decide (1 < lane))),
       (237,.pred (decide (3 < lane))),(236,.pred (decide (7 < lane))),
       (235,.pred (decide (15 < lane)))]
    seg_fp hs using simp [compare,truncBits_ofNat hL32 (by decide),toNat_ofNat_lt hL64,
      show (truncBits 32 15#64).toNat = 15 by decide,
      show (truncBits 32 7#64).toNat = 7 by decide,
      show (truncBits 32 3#64).toNat = 3 by decide,
      show (truncBits 32 1#64).toNat = 1 by decide,
      show (truncBits 32 0#64).toNat = 0 by decide]
  have hv' : At v 1766 ([(1073,b32 lane)]++(7137,b32 p.heads)::F) := hv.mono
    ⟨holds_mem hv.2.2.2.2 (by simp [F,firstGroupCarry,firstDrainTail,drainSchedulerFrame,lane]),
      hv.2.2.2.2⟩
  obtain ⟨u,hGuard,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hGuard hv'
  obtain ⟨hPred,hRest⟩ := (holds_append ..).mp hU.2.2.2.2
  refine ⟨u,(run_rtg hLoadAll).trans (run_rtg hGuard),hU.mono ?_⟩
  change Holds u.regs
    (((7187,b32 (groupLaneTiles p 0 lane))::cacheDrainGuardFrame false lane) ++
      (7137,b32 p.heads) :: firstGroupCarry p l g use)
  exact (holds_append ..).mpr ⟨⟨hRest.2.1,hPred⟩,hRest.1,hRest.2.2⟩

/-- The returned terminal group endpoints set up all lane contributions and
guards for the loader's real first prefix scan. -/
theorem CacheDrainNeighbors.firstGroupOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g use : Nat} (hg : g < l.threads)
    (c : CacheDrainNeighbors p l X g use) :
    Nonempty (SchedulerWarpReached l X g 1771
      (fun lane => firstGroupScanFrame p l (warpLane l g lane) use) c.shuffles c.votes c.ends) := by
  apply c.reached.advanceLocal
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hlane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hSrc := Step.shflSource_lt .down hl 1 31
  have hWord : laneOf l (warpLane l g (shflSource .down lane 1 31).1) =
      (shflSource .down lane 1 31).1 := (Step.sameWarp_lane hBlock hg hSrc).2
  have hAt := c.reached.checkpoint lane hl
  have hStart : At (c.reached.state lane) 1752
      ([(2239,b32 (drainCuQ p (shflSource .down (laneOf l (warpLane l g lane)) 1 31).1)),
        (7184,b32 (drainCuQ p (laneOf l (warpLane l g lane))))] ++
        firstGroupCarry p l (warpLane l g lane) use) := by
    rw [hlane]
    simpa only [hWord,firstDrainWordsFrame,firstGroupCarry,hlane,List.cons_append,
      List.nil_append] using hAt
  obtain ⟨u,hu,hU⟩ := firstGroupCountLocal hp hStart
  obtain ⟨v,hv,hV⟩ := prepareFirstGroupScan hp hU
  exact ⟨v,hu.trans hv,hV⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
