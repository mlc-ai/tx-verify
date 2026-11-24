-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSchedulerWarp
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part121

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem schedulerCoreSlice :
    ((kernel.code.drop 7763).take 44).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 10000 in kernel_rfl

theorem correctionSchedulerOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 7763 ≤ t.pc) (hHi : t.pc < 7807) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 7763).take 44 := by
      apply List.mem_of_getElem? (i := t.pc - 7763)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp schedulerCoreSlice _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

theorem correctionLinear {l : Launch} {g pc n : Nat} {t u : TState} {regs : List Nat}
    (hLo : 7763 ≤ pc) (hHi : pc + n ≤ 7807) (ht : t.pc = pc)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun i => regs.all (fun r => !(writesRegs i.op).contains r)) = true)
    (hFallthrough : ((kernel.code.drop pc).take (n - 1)).all
      (fun i => schedulerFallsThrough i.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧
      ∀ r ∈ regs, u.regs r = t.regs r := by
  have hlo : pc ≤ t.pc := ht.ge
  have hhi : t.pc + n ≤ pc + n := by rw [ht]
  exact ⟨schedulerLocalTransport hFallthrough
    (fun ha hb => correctionSchedulerOut (by omega) (by omega)) hr hlo hhi,
    fun _ h => schedulerLocalFrame hWrites hFallthrough hr hlo hhi h⟩

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem correctionFirstTileGate (l : Launch) (g : Nat) {lane batch begin finish : Nat}
    (hl : lane < 32) (hb : batch < 2 ^ 31) (hBegin : begin < 2 ^ 32)
    (hFinish : finish < 2 ^ 32) :
    Seg kernel [] l g 6 7763
      [(1616, b32 lane), (7277, b32 batch), (7267, b32 begin), (5869, b32 finish)] 7769
      [(1617, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
        (7270, b32 0), (17, .pred (decide (laneHasRequest lane batch))),
        (685, .pred (!decide (laneHasRequest lane batch)))] := by
  intro t ht
  have hL32 : lane < 2 ^ 32 := by omega
  have hL31 : lane < 2 ^ 31 := by omega
  have hL64 : lane < 2 ^ 64 := by omega
  have hB32 : batch < 2 ^ 32 := by omega
  have hNe : (lane : Int) ≠ 31 ↔ lane < 31 := by omega
  have hi : (↑(truncBits 32 (BitVec.ofInt 64 31)).toNat : Int) = 31 := rfl
  seg_fp ht using
    first
    | rfl
    | simp only [truncBits_ofNat hBegin (by decide), truncBits_ofNat hFinish (by decide)]
    | (simp only [compare, Option.getD_some, truncBits_ofNat hL32 (by decide),
        truncBits_ofNat hB32 (by decide), signedWord hL31, signedWord hb,
        toNat_ofNat_lt hL64, Int.ofNat_lt, Bool.and_comm, hi, hNe]
       by_cases hcut : lane < batch <;> by_cases hlast : lane < 31 <;>
         simp [laneHasRequest, hcut, hlast])

private inductive TileCountSite
  | first | fallback | drainFirst | drainLater

private def TileCountSite.start : TileCountSite → Nat
  | .first => 7770
  | .fallback => 7829
  | .drainFirst => 9094
  | .drainLater => 9152

private def TileCountSite.lengthReg : TileCountSite → Nat
  | .first => 1617
  | .fallback => 1622
  | .drainFirst => 1657
  | .drainLater => 1661

private def TileCountSite.quotientReg : TileCountSite → Nat
  | .first => 5873
  | .fallback => 5894
  | .drainFirst => 7086
  | .drainLater => 7107

private def TileCountSite.remainderPred : TileCountSite → Nat
  | .first => 688
  | .fallback => 702
  | .drainFirst => 747
  | .drainLater => 761

private def TileCountSite.resultReg : TileCountSite → Nat
  | .first | .fallback => 7270
  | .drainFirst | .drainLater => 7282

private theorem tileCountQuotient (site : TileCountSite) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 8 site.start
    [(site.lengthReg, b32 len)] (site.start+8)
    [(site.quotientReg, b32 (len / 256)),
     (site.remainderPred, .pred (decide (len ≠ len / 256 * 256)))] := by
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
  cases site <;> intro t ht <;> seg_fp ht using
    simp only [b32, s31, s8, s24, ite_eq_right h24, shr31, shr8, z, z32, zShift,
      aZero, truncBits_ofNat h32 (by decide), m32,
      truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
      Option.getD_some, signedWord h31, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
      toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
    all_goals
      simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowByteMask h32,
        truncBits_ofNat hMask (by decide),
        toNat_ofNat_lt (show len / 256 * 256 < 2 ^ 64 by omega)]

private theorem tileCountAddRemainder (site : TileCountSite) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 2 (site.start+8)
    [(site.quotientReg, b32 (len / 256)),
     (site.remainderPred, .pred (decide (len ≠ len / 256 * 256)))]
    (site.start+10)
    [(site.resultReg, b32 ((len + 255) / 256))] := by
  by_cases h : len = len / 256 * 256
  · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
    cases site <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
  · cases site <;> intro t ht <;>
      simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits

private theorem roundUpTileCount (site : TileCountSite) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 site.start [(site.lengthReg,b32 len)] (site.start+10)
      [(site.resultReg,b32 ((len+255)/256))] := by
  exact (tileCountQuotient site l g hlen).comp (tileCountAddRemainder site l g hlen)

/-- Both opening scans round the query length up to 256-row tiles. -/
theorem correctionScanTileCount (fallback : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (if fallback then 7829 else 7770)
      [(if fallback then 1622 else 1617, b32 len)] (if fallback then 7839 else 7780)
      [(7270, b32 ((len + 255) / 256))] := by
  cases fallback
  · exact roundUpTileCount .first l g hlen
  · exact roundUpTileCount .fallback l g hlen

/-- The initial and later drain scans use the same rounded division. -/
theorem correctionDrainTileCount (later : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (if later then 9152 else 9094)
      [(if later then 1661 else 1657,b32 len)] (if later then 9162 else 9104)
      [(7282,b32 ((len+255)/256))] := by
  cases later
  · exact roundUpTileCount .drainFirst l g hlen
  · exact roundUpTileCount .drainLater l g hlen

private theorem headsParameterName :
    param 17 =
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

private theorem loadHeadsWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (hpc : t.pc = 7780) (hf : t.fault = none) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t 7142 (b32 p.heads))) := by
  obtain ⟨hHeads, hParam⟩ := hp.values (17, p.heads) (by simp [Params.scalarWords])
  change l.params (param 17) = some (BitVec.ofNat 64 p.heads) at hParam
  rw [headsParameterName] at hParam
  have he : execLocalA [] l g t (kernel.code[7780]?.getD (⟨none, .exit⟩ : Instr)).op =
      .ok (next (setReg t 7142 (b32 p.heads))) := by
    rw [Flow.code_7780, Option.getD_some, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure,
      truncBits_ofNat hHeads (by decide)]
    rfl
  have hRun : run kernel [] l g 1 t = some (next (setReg t 7142 (b32 p.heads))) := by
    rw [Flow.code_7780, Option.getD_some] at he
    simp only [run, tauStep, out, hpc, hf, Flow.code_7780, guardHolds, pure, Except.pure, he]
    rfl
  exact (correctionLinear (regs := []) (by decide) (by decide) hpc (by
    set_option maxRecDepth 100000 in kernel_rfl) rfl hRun).1

private theorem firstWord_eq_drain (p : Params) (i : Nat) :
    firstSchedulerWord p i = drainCuQ p i := by
  by_cases h : p.batch < i
  · simp [firstSchedulerWord, drainCuQ, h, Nat.not_le.mpr h]
  · simp [firstSchedulerWord, drainCuQ, h, Nat.le_of_not_gt h]

/-- Register state preserved through the first loader scan's shuffle-up rounds. -/
def firstCorrectionScanFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7270, b32 (groupLaneTiles p 0 (laneOf l g))), (7142, b32 p.heads),
   (17, .pred (decide (laneHasRequest (laneOf l g) p.batch)))] ++ firstShuffleFacts p l g

/-- Turn the actual down-shuffle endpoints into the first scan's input, including the
batch-sentinel zero contribution and the ABI head count load. -/
theorem correctionFirstTilesWithGuard {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (ht : At t 7763 ((5869, b32 (firstSchedulerWord p (shflSource .down (laneOf l g) 1 31).1)) ::
      firstShuffleFacts p l g)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 7781 ((685,.pred (!decide (laneHasRequest (laneOf l g) p.batch))) ::
        firstCorrectionScanFacts p l g) := by
  let lane := laneOf l g
  let active := decide (laneHasRequest lane p.batch)
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  let keep := (firstShuffleFacts p l g).map Prod.fst
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  have hBatch := holds_lookup ht.2.2.2.2.2
    (show (firstShuffleFacts p l g).lookup 7277 = some (b32 p.batch) from rfl)
  have hAt : At t 7763
      [(1616, b32 lane), (7277, b32 p.batch), (7267, b32 begin), (5869, b32 finish)] := by
    apply ht.mono
    refine ⟨ht.2.2.2.2.2.2.1, hBatch, ?_, ?_, trivial⟩
    · simpa only [firstWord_eq_drain] using ht.2.2.2.2.2.1
    · simpa only [firstWord_eq_drain] using ht.2.2.2.2.1
  obtain ⟨v, hv, hV⟩ := correctionFirstTileGate l g hl hp.shape.2.1 hBegin hFinish t hAt
  obtain ⟨hvA, hvFrame⟩ := correctionLinear (regs := keep) (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep := holdsSchedulerFrame ht.2.2.2.2.2 hvFrame (fun _ h => List.mem_map_of_mem h)
  let carry := (17, .pred active) :: firstShuffleFacts p l g
  let guarded := (685,.pred (!active)) :: carry
  have hBranchAt : At v 7769
      ((685, .pred (!active)) :: (1617, .bits 32 diff) :: (7270, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_7769 (!active) hBranchAt hBranchAt.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := correctionLinear (regs := []) (by decide) (by decide) hBranchAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  have hGroup : ∃ n u, run kernel Assumptions.all l g n w = some u ∧
      At u 7780 ((7270, b32 (groupLaneTiles p 0 lane)) :: guarded) := by
    by_cases ha : active = true
    · have hPc : w.pc = 7770 := by simpa [ha] using hW.1
      have hRewrite : diff = BitVec.ofNat 64 (finish - begin) := by
        dsimp [diff]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono ha),
          truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
      have hLen : At w 7770 [(1617, b32 (finish - begin))] :=
        ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
          by simpa [b32, hRewrite] using hW.2.2.2.2.2.1, trivial⟩
      obtain ⟨u, hu, hU⟩ := correctionScanTileCount false l g hLength w hLen
      obtain ⟨huA, huFrame⟩ := correctionLinear (regs := 685 :: 17 :: keep)
        (by decide) (by decide) hPc (by
        set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hu
      have hCarry : Holds w.regs guarded := ⟨hW.2.2.2.2.1,hW.2.2.2.2.2.2.2⟩
      have hSaved : Holds u.regs guarded := holdsSchedulerFrame hCarry huFrame (fun _ h =>
        List.mem_map_of_mem h)
      have hCount : (finish - begin + 255) / 256 = groupLaneTiles p 0 lane := by
        change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
        rwa [ite_eq_left ha] at hTiles
      refine ⟨10, u, huA, hU.mono ⟨?_, hSaved⟩⟩
      have hReg := hU.2.2.2.2.1
      change u.regs 7270 = some (b32 ((finish - begin + 255) / 256)) at hReg
      rw [hCount] at hReg
      exact hReg
    · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
      have hPc : w.pc = 7780 := by simpa [ha'] using hW.1
      have hCount : 0 = groupLaneTiles p 0 lane := by
        change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
        rwa [ite_eq_right ha] at hTiles
      exact ⟨0, w, rfl, ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
        ⟨by simpa only [← hCount] using hW.2.2.2.2.2.2.1,
          hW.2.2.2.2.1,hW.2.2.2.2.2.2.2⟩⟩⟩
  obtain ⟨n, u, hu, hU⟩ := hGroup
  have hFresh : ∀ x ∈ ((7270, b32 (groupLaneTiles p 0 lane)) :: guarded), x.1 ≠ 7142 := by
    intro pair hm heq
    have hMap := List.mem_map_of_mem (f := Prod.fst) hm
    rw [heq] at hMap
    exact (of_decide_eq_true rfl : 7142 ∉ 7270 :: 685 :: 17 :: keep) hMap
  have hFinal := hU.set (v := b32 p.heads) hFresh
  exact ⟨6 + 1 + n + 1, _, run_comp (run_comp (run_comp hvA hwA) hu)
    (loadHeadsWord hp hU.1 hU.2.2.2.1), hFinal.mono
    ⟨hFinal.2.2.2.2.2.2.1,hFinal.2.2.2.2.2.1,hFinal.2.2.2.2.1,
      hFinal.2.2.2.2.2.2.2⟩⟩

/-- The opening down-shuffle readies the first correction scan. -/
theorem correctionFirstTiles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState}
    (ht : At t 7763 ((5869, b32 (firstSchedulerWord p (shflSource .down (laneOf l g) 1 31).1)) ::
      firstShuffleFacts p l g)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 7781 (firstCorrectionScanFacts p l g) := by
  obtain ⟨n,u,hRun,hAt⟩ := correctionFirstTilesWithGuard hp ht
  exact ⟨n,u,hRun,hAt.mono hAt.2.2.2.2.2⟩

/-- Every lane enters the first up-scan with the tile count from its own cuQ endpoints. -/
theorem correctionWarpFirstTilesAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes : Nat} (hg : g < l.threads)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 7763
      (fun lane => (5869, b32 (firstSchedulerWord p (shflSource .down lane 1 31).1)) ::
        firstShuffleFacts p l (warpLane l g lane)) shuffles votes ends) :
    ∃ next : SchedulerWarpAt l X g 7781
      (fun lane => firstCorrectionScanFacts p l (warpLane l g lane)) shuffles votes ends,
        next.pos = cur.pos := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  apply cur.advanceLocalAt
  intro lane hLane
  have hThreadLane : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hLane).2
  obtain ⟨_, u, hu, hState⟩ := correctionFirstTiles hp (show At (cur.state lane) 7763
    ((5869, b32 (firstSchedulerWord p (shflSource .down
      (laneOf l (warpLane l g lane)) 1 31).1)) :: firstShuffleFacts p l (warpLane l g lane)) by
    rw [hThreadLane]
    exact cur.checkpoint lane hLane)
  exact ⟨u, run_rtg hu, hState⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
