-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderCuQ
public import Kernels.TmlFa4Fwd.Proof.EpilogueSchedule
public import Kernels.TmlFa4Fwd.Flow.Code.Part003
public import Kernels.TmlFa4Fwd.Flow.Code.Part004

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem loaderFirstTileGate (l : Launch) (g : Nat) {lane batch begin finish : Nat}
    (hl : lane < 32) (hb : batch < 2 ^ 31) (hBegin : begin < 2 ^ 32)
    (hFinish : finish < 2 ^ 32) :
    Seg kernel [] l g 6 188
      [(1073, b32 lane), (7170, b32 batch), (7159, b32 begin), (1707, b32 finish)] 194
      [(1074, .bits 32 (truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin))),
        (7162, b32 0), (3, .pred (decide (laneHasRequest lane batch))),
        (64, .pred (!decide (laneHasRequest lane batch)))] := by
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

/-- The first and subsequent loader groups use the same ten-instruction rounding sequence. -/
def loaderCeilSite (later : Bool) : CeilSite :=
  if later then ⟨253, 1078, 1732, 81, 7162⟩ else ⟨195, 1074, 1711, 67, 7162⟩

theorem loaderLaneTileCount (later : Bool) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 30) :
    Seg kernel [] l g 10 (loaderCeilSite later).pc [((loaderCeilSite later).lengthReg, b32 len)]
      ((loaderCeilSite later).pc + 10)
      [((loaderCeilSite later).countReg, b32 ((len + 255) / 256))] := by
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
  have hFirst : Seg kernel [] l g 8 (loaderCeilSite later).pc
      [((loaderCeilSite later).lengthReg, b32 len)] ((loaderCeilSite later).pc + 8)
      [((loaderCeilSite later).quotientReg, b32 (len / 256)),
       ((loaderCeilSite later).remainderPred, .pred (decide (len ≠ len / 256 * 256)))] := by
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
  have hLast : Seg kernel [] l g 2 ((loaderCeilSite later).pc + 8)
      [((loaderCeilSite later).quotientReg, b32 (len / 256)),
       ((loaderCeilSite later).remainderPred, .pred (decide (len ≠ len / 256 * 256)))]
      ((loaderCeilSite later).pc + 10)
      [((loaderCeilSite later).countReg, b32 ((len + 255) / 256))] := by
    by_cases h : len = len / 256 * 256
    · have hPad : decide (len ≠ len / 256 * 256) = false := decide_eq_false (fun hn => hn h)
      cases later <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
    · cases later <;> intro t ht <;>
        simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

private theorem loadHeadsWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (hpc : t.pc = 205) (hf : t.fault = none) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t 7136 (b32 p.heads))) := by
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
  obtain ⟨hHeads, hParam⟩ := hp.values (17, p.heads) (by simp [Params.scalarWords])
  change l.params (param 17) = some (BitVec.ofNat 64 p.heads) at hParam
  rw [hName] at hParam
  have he : execLocalA [] l g t (kernel.code[205]?.getD (⟨none, .exit⟩ : Instr)).op =
      .ok (next (setReg t 7136 (b32 p.heads))) := by
    rw [Flow.code_205, Option.getD_some, execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq,
      hParam, DType.width, MemExt.extendBits_same, pure, Except.pure,
      truncBits_ofNat hHeads (by decide)]
    rfl
  have hRun : run kernel [] l g 1 t = some (next (setReg t 7136 (b32 p.heads))) := by
    rw [Flow.code_205, Option.getD_some] at he
    simp only [run, tauStep, out, hpc, hf, Flow.code_205, guardHolds, pure, Except.pure, he]
    rfl
  exact (loaderLinear (regs := []) (by decide) (by decide) hpc (by
    set_option maxRecDepth 100000 in kernel_rfl) rfl hRun).1

/-- Register state preserved through the first loader scan's shuffle-up rounds. -/
def firstLoaderScanFacts (p : Params) (l : Launch) (g warp : Nat) : List (Nat × Value) :=
  [(7162, b32 (groupLaneTiles p 0 (laneOf l g))), (7136, b32 p.heads),
   (3, .pred (decide (laneHasRequest (laneOf l g) p.batch)))] ++ loaderCuQFacts p l g warp

/-- Turn the actual down-shuffle endpoints into the first scan's input, including the
batch-sentinel zero contribution and the ABI head count load. -/
theorem loaderFirstTiles {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g warp : Nat} {t : TState}
    (ht : At t 188 ((1707, b32 (drainCuQ p (shflSource .down (laneOf l g) 1 31).1)) ::
      loaderCuQFacts p l g warp)) :
    ∃ n u, run kernel Assumptions.all l g n t = some u ∧
      At u 206 (firstLoaderScanFacts p l g warp) := by
  let lane := laneOf l g
  let active := decide (laneHasRequest lane p.batch)
  let begin := drainCuQ p lane
  let finish := drainCuQ p (shflSource .down lane 1 31).1
  let diff := truncBits 32 (BitVec.ofNat 64 finish - BitVec.ofNat 64 begin)
  let keep := (loaderCuQFacts p l g warp).map Prod.fst
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨hBegin, hFinish, hMono, hLength, hTiles⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at hBegin hFinish hMono hLength hTiles
  have hAt : At t 188
      [(1073, b32 lane), (7170, b32 p.batch), (7159, b32 begin), (1707, b32 finish)] :=
    ht.mono ⟨ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.1, trivial⟩
  obtain ⟨v, hv, hV⟩ := loaderFirstTileGate l g hl hp.shape.2.1 hBegin hFinish t hAt
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := keep) (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hKeep := holdsSchedulerFrame ht.2.2.2.2.2 hvFrame (fun _ h => List.mem_map_of_mem h)
  let carry := (3, .pred active) :: loaderCuQFacts p l g warp
  have hBranchAt : At v 194
      ((64, .pred (!active)) :: (1074, .bits 32 diff) :: (7162, b32 0) :: carry) :=
    hV.mono ⟨hV.2.2.2.2.2.2.2.1, hV.2.2.2.2.1, hV.2.2.2.2.2.1, hV.2.2.2.2.2.2.1, hKeep⟩
  obtain ⟨w, hw, hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_194 (!active) hBranchAt hBranchAt.2.2.2.2.1 (by simp)
  obtain ⟨hwA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hBranchAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) rfl hw
  have hGroup : ∃ n u, run kernel Assumptions.all l g n w = some u ∧
      At u 205 ((7162, b32 (groupLaneTiles p 0 lane)) :: carry) := by
    by_cases ha : active = true
    · have hPc : w.pc = 195 := by simpa [ha] using hW.1
      have hRewrite : diff = BitVec.ofNat 64 (finish - begin) := by
        dsimp [diff]
        rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show begin < 2 ^ 64 by omega) (hMono ha),
          truncBits_ofNat (show finish - begin < 2 ^ 32 by omega) (by decide)]
      have hLen : At w 195 [(1074, b32 (finish - begin))] :=
        ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
          by simpa [b32, hRewrite] using hW.2.2.2.2.2.1, trivial⟩
      obtain ⟨u, hu, hU⟩ := loaderLaneTileCount false l g hLength w hLen
      obtain ⟨huA, huFrame⟩ := loaderLinear (regs := 3 :: keep) (by decide) (by decide) hPc (by
        set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hu
      have hCarry : Holds w.regs carry := hW.2.2.2.2.2.2.2
      have hSaved : Holds u.regs carry := holdsSchedulerFrame hCarry huFrame (fun _ h =>
        List.mem_map_of_mem h)
      have hCount : (finish - begin + 255) / 256 = groupLaneTiles p 0 lane := by
        change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
        rwa [ite_eq_left ha] at hTiles
      refine ⟨10, u, huA, hU.mono ⟨?_, hSaved⟩⟩
      have hReg := hU.2.2.2.2.1
      change u.regs 7162 = some (b32 ((finish - begin + 255) / 256)) at hReg
      rw [hCount] at hReg
      exact hReg
    · have ha' : active = false := Bool.eq_false_of_not_eq_true ha
      have hPc : w.pc = 205 := by simpa [ha'] using hW.1
      have hCount : 0 = groupLaneTiles p 0 lane := by
        change (if active then (finish - begin + 255) / 256 else 0) = _ at hTiles
        rwa [ite_eq_right ha] at hTiles
      exact ⟨0, w, rfl, ⟨hPc, hW.2.1, hW.2.2.1, hW.2.2.2.1,
        by simpa only [← hCount] using hW.2.2.2.2.2.2⟩⟩
  obtain ⟨n, u, hu, hU⟩ := hGroup
  have hFresh : ∀ x ∈ ((7162, b32 (groupLaneTiles p 0 lane)) :: carry), x.1 ≠ 7136 := by
    intro pair hm heq
    have hMap := List.mem_map_of_mem (f := Prod.fst) hm
    rw [heq] at hMap
    exact (of_decide_eq_true rfl : 7136 ∉ 7162 :: 3 :: keep) hMap
  have hFinal := hU.set (v := b32 p.heads) hFresh
  exact ⟨6 + 1 + n + 1, _, run_comp (run_comp (run_comp hvA hwA) hu)
    (loadHeadsWord hp hU.1 hU.2.2.2.1), hFinal.mono
    ⟨hFinal.2.2.2.2.2.1, hFinal.2.2.2.2.1, hFinal.2.2.2.2.2.2⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
