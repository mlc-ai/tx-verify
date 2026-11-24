-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderTripCount
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstRound
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Kernels.TmlFa4Fwd.Flow.Code.Part053
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreStart
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

private structure GeometryCeil where
  pc : Nat
  length : Nat
  quotient : Nat
  remainder : Nat
  count : Nat

private def geometryCeil : Fin 3 → GeometryCeil
  | 0 => ⟨3374, 1224, 2853, 485, 2856⟩
  | 1 => ⟨3388, 1225, 2863, 488, 2866⟩
  | 2 => ⟨3405, 2871, 2875, 491, 2878⟩

private theorem geometryBlockCeil (site : Fin 3) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 31) :
    Seg kernel Assumptions.all l g 10 (geometryCeil site).pc
      [((geometryCeil site).length, b32 len)]
      ((geometryCeil site).pc + 10) [((geometryCeil site).count, b32 ((len+127)/128))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 128 < 2 ^ 32 := by omega
  have hMask : len / 128 * 128 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr7 : (len : Int) / 2 ^ 7 = (len / 128 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s7 : min (truncBits 32 (BitVec.ofInt 64 7)).toNat 32 = 7 := rfl
  have s25 : (truncBits 32 (BitVec.ofInt 64 25)).toNat = 25 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 25 = 0 := rfl
  have h25 : ¬25 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-128)) = BitVec.ofNat 64 4294967168 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel Assumptions.all l g 8 (geometryCeil site).pc
      [((geometryCeil site).length, b32 len)] ((geometryCeil site).pc + 8)
      [((geometryCeil site).quotient, b32 (len/128)),
       ((geometryCeil site).remainder, .pred (decide (len ≠ len/128*128)))] := by
    fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s7, s25, ite_eq_right h25, shr31, shr7, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, Loader.int32Signed hlen, hNeg, gt_iff_lt, hPos, decide_true,
        Bool.true_and, toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, Loader.lowSevenMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 128 * 128 < 2 ^ 64 by omega)]
  have hLast : Seg kernel Assumptions.all l g 2 ((geometryCeil site).pc + 8)
      [((geometryCeil site).quotient, b32 (len/128)),
       ((geometryCeil site).remainder, .pred (decide (len ≠ len/128*128)))]
      ((geometryCeil site).pc + 10) [((geometryCeil site).count, b32 ((len+127)/128))] := by
    by_cases h : len = len/128*128
    · have hPad : decide (len ≠ len/128*128) = false := decide_eq_false (fun hn => hn h)
      fin_cases site <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
    · fin_cases site <;> intro t ht <;>
        simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

/-- A positive query length is subtracted using its signed 32-bit representation. -/
theorem negativeLengthWord {q : Nat} (hq : q < 2^32) (hPos : 0 < q) :
    maskSigned (-(q : Int)) = b32 (2^32-q) := by
  unfold maskSigned b32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

private theorem negativeLengthReadBits {q : Nat} (hq : q < 2^32) (hPos : 0 < q) :
    truncBits 32 ((BitVec.ofInt 32 (-(q : Int))).setWidth 64) =
      BitVec.ofNat 64 (2^32-q) := by
  have h := negativeLengthWord hq hPos
  change Value.bits 32 ((BitVec.ofInt 32 (-(q : Int))).setWidth 64) =
    Value.bits 32 (BitVec.ofNat 64 (2^32-q)) at h
  rw [(Value.bits.inj h).2, truncBits_ofNat (show 2^32-q < 2^32 by omega) (by decide)]

private theorem fullCausalLength (l : Launch) (g key query tile : Nat)
    (hLen : 0 < query ∧ query ≤ key)
    (hKey : key < 2^31)
    (hSum : key-query+256*(tile+1) < 2^31) :
    Seg kernel Assumptions.all l g 4 3384
      [(7246, b32 tile), (1224, b32 key), (1223, maskSigned (-(query : Int)))]
      3388 [(1225, b32 (key-query+256*(tile+1)))] := by
  intro t ht
  have hQ := hLen.2
  have hNeg := negativeLengthReadBits (q := query) (by omega) hLen.1
  seg_fp ht using norm_bits [hNeg]

private theorem minGeometryCount (site : Fin 2) (l : Launch) (g k q : Nat)
    (hk : k < 2^31) (hq : q < 2^31) :
    Seg kernel Assumptions.all l g 1 (if site.val = 0 then 3398 else 3415)
      [(2856, b32 k), ((if site.val = 0 then 2866 else 2878), b32 q)]
      (if site.val = 0 then 3399 else 3416)
      [((if site.val = 0 then 1226 else 2879), b32 (min k q))] := by
  have h32k : k < 2^32 := by omega
  have h32q : q < 2^32 := by omega
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  by_cases h : k < q
  · fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32q (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, ite_true, ite_false, Loader.int32Signed hk,
        Loader.int32Signed hq, Int.ofNat_lt, h, decide_true,
        min_eq_left h.le]
  · have hle : q ≤ k := by omega
    fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32q (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, ite_true, Loader.int32Signed hk,
        Loader.int32Signed hq, Int.ofNat_lt, h, decide_false, ite_false, min_eq_right hle]

private theorem singleStageLength (l : Launch) (g key query tile : Nat) (stage : Fin 2)
    (hLen : 0 < query ∧ query ≤ key) (hKey : key < 2^31)
    (hTile : 256*tile < query) (hSum : key-query+256*(tile+1) < 2^31) :
    Seg kernel Assumptions.all l g 6 3399
      [(7246, b32 tile), (2772, b32 stage.val), (1224, b32 key),
        (1223, maskSigned (-(query : Int)))] 3405
      [(2868, b32 (128*(2*tile+stage.val))),
        (2871, b32 (key-query+128*(2*tile+stage.val+1)))] := by
  have hStage := stage.isLt
  have h2 : tile*2 < 2^32 := by omega
  have hBase : 128*(2*tile+stage.val) < 2^32 := by omega
  have hSmall : 2*tile+stage.val < 4294967296 := by omega
  have hOr : tile*2 ||| stage.val = 2*tile+stage.val := by
    rw [Nat.mul_comm tile 2]
    exact (Nat.two_pow_add_eq_or_of_lt (i := 1) hStage tile).symm
  have hOrN : ((tile % 2^32 * 2) % 2^32) ||| (stage.val % 2^32) = 2*tile+stage.val := by
    rw [Nat.mod_eq_of_lt (show tile < 2^32 by omega), Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt (show stage.val < 2^32 by omega), hOr]
  have hQ := hLen.2
  have hNeg := negativeLengthReadBits (q := query) (by omega) hLen.1
  simp only [Nat.reducePow] at hOrN hBase
  intro t ht
  seg_fp ht using norm_bits [hNeg, hOrN, Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hSmall]

private theorem firstBiasCapSegment (l : Launch) (g blocks stageBlocks : Nat)
    (hStage : stageBlocks ≤ blocks) (hBound : blocks + 10 < 2^31) :
    Seg kernel Assumptions.all l g 2 3416 [(1226, b32 blocks), (2879, b32 stageBlocks)]
      3418 [(1228, b32 (blocks-stageBlocks+10))] := by
  intro t ht
  seg_fp ht using norm_bits

private theorem geometryCode (i : Fin 44) :
    ∃ ins, kernel.code[3374+i.val]? = some ins ∧
      Assumptions.coreOp ins.op = true ∧ nextPc ins.op (3374+i.val) = 3374+i.val+1 ∧
      (∀ target, ¬ BrxTarget ins.op target) := by
  fin_cases i
  · exact ⟨_, Flow.code_3374, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3375, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3376, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3377, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3378, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3379, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3380, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3381, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3382, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3383, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3384, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3385, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3386, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3387, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3388, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3389, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3390, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3391, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3392, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3393, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3394, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3395, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3396, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3397, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3398, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3399, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3400, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3401, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3402, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3403, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3404, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3405, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3406, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3407, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3408, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3409, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3410, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3411, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3412, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3413, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3414, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3415, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3416, rfl, rfl, fun _ => nofun⟩
  · exact ⟨_, Flow.code_3417, rfl, rfl, fun _ => nofun⟩

theorem geometryFrame {l : Launch} {g pc steps : Nat} {t u : TState} {keep : List Nat}
    (hLower : 3374 ≤ pc) (hUpper : pc+steps ≤ 3418) (hPc : t.pc = pc)
    (hAudit : ((kernel.code.drop pc).take steps).all
      (fun ins => keep.all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hr : run kernel Assumptions.all l g steps t = some u) :
    ∀ r ∈ keep, u.regs r = t.regs r := by
  apply fixedFrame (first := pc) (stop := pc+steps) _ _ (by omega) (by omega) hr
  · intro ip hLo hHi
    let i : Fin 44 := ⟨ip-3374, by omega⟩
    have he : 3374+i.val = ip := by dsimp [i]; omega
    obtain ⟨ins, hCode, hCore, hNext, hNoBrx⟩ := geometryCode i
    rw [he] at hCode hNext
    refine ⟨ins, hCode, hCore, hNext, hNoBrx, fun r hm => ?_⟩
    have hMem : ins ∈ (kernel.code.drop pc).take steps := by
      apply List.mem_of_getElem? (i := ip-pc)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hCode]
    have h := List.all_eq_true.mp (List.all_eq_true.mp hAudit ins hMem) r hm
    simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using h
  · intro ip hLo hHi
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- Exact causal key bound and clipped block count of one of the two softmax stages. -/
def stageGeometryBlocks (p : Params) (batch tile : Nat) (stage : Fin 2) : Nat :=
  min ((p.kLength batch+127)/128)
    ((p.kLength batch-p.qLength batch+128*(2*tile+stage.val+1)+127)/128)

def firstGeometryInput (p : Params) (batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  [(1223, maskSigned (-(p.qLength batch : Int))), (1224, b32 (p.kLength batch)),
    (7246, b32 tile), (2772, b32 stage.val)]

def firstGeometryFacts (p : Params) (batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  let blocks := Mma.trips p batch tile
  [(1223, maskSigned (-(p.qLength batch : Int))), (1224, b32 (p.kLength batch)),
    (2868, b32 (128*(2*tile+stage.val))),
    (1225, b32 (p.kLength batch-p.qLength batch+256*(tile+1))), (1226, b32 blocks),
    (1228, b32 (blocks-stageGeometryBlocks p batch tile stage+10))]

variable {p : Params} {l : Launch} {m : Mem0}

/-- The 44 instructions after the used-K load compute the exact full-tile and stage block
limits, including the boundary that splits the two repeated softmax loops. -/
theorem firstGeometrySegment (hp : Pre p l m) (g batch tile : Nat) (stage : Fin 2)
    (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch) :
    Seg kernel Assumptions.all l g 44 3374 (firstGeometryInput p batch tile stage)
      3418 (firstGeometryFacts p batch tile stage) := by
  let key := p.kLength batch
  let query := p.qLength batch
  let upper := key-query+256*(tile+1)
  let edge := key-query+128*(2*tile+stage.val+1)
  let keyBlocks := (key+127)/128
  let upperBlocks := (upper+127)/128
  let stageBlocks := (edge+127)/128
  let blocks := Mma.trips p batch tile
  let clipped := stageGeometryBlocks p batch tile stage
  have hStage := stage.isLt
  have hLen : 0 < query ∧ query ≤ key := ⟨by dsimp [query]; omega, (hp.lengths batch hb).2.1⟩
  have hKey : key < 2^31 := by
    have := (hp.lengths batch hb).2.2
    dsimp [key]
    omega
  have hTrips := Mma.trips_bounds hp hb hTile
  have hUpper : upper < 2^31 := hTrips.2.2
  have hEdge : edge < 2^31 := by dsimp [edge, upper] at *; omega
  have hClipped : clipped ≤ blocks := by
    dsimp [clipped, blocks, stageGeometryBlocks, Mma.trips]
    omega
  have hBlocks := hTrips.2.1
  have hBound : blocks+10 < 2^31 := by dsimp [key] at hKey; omega
  intro t ht
  obtain ⟨a, haRun, ha⟩ := (geometryBlockCeil 0 l g hKey).apply (ht.mono
    ⟨ht.2.2.2.2.2.1, trivial⟩)
  have haKeep := geometryFrame (keep := [7246, 1224, 1223]) (by decide) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl) haRun
  have ha' : At a 3384 [(7246, b32 tile), (1224, b32 key), (1223, maskSigned (-(query : Int)))] :=
    ha.mono ⟨(haKeep _ (by decide)).trans ht.2.2.2.2.2.2.1,
      (haKeep _ (by decide)).trans ht.2.2.2.2.2.1,
      (haKeep _ (by decide)).trans ht.2.2.2.2.1, trivial⟩
  obtain ⟨b, hbRun, hbAt⟩ := (fullCausalLength l g key query tile hLen hKey hUpper).apply ha'
  obtain ⟨c, hcRun, hcAt⟩ := (geometryBlockCeil 1 l g hUpper).apply hbAt
  have hab := run_comp haRun hbRun
  have habc := run_comp hab hcRun
  have hcKeep := geometryFrame (keep := [2856]) (by decide) (by decide) ha'.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp hbRun hcRun)
  have hc' : At c 3398 [(2856, b32 keyBlocks), (2866, b32 upperBlocks)] :=
    hcAt.mono ⟨(hcKeep _ (by decide)).trans ha.2.2.2.2.1, hcAt.2.2.2.2.1, trivial⟩
  obtain ⟨d, hdRun, hdAt⟩ := (minGeometryCount 0 l g keyBlocks upperBlocks
    (by dsimp [keyBlocks]; omega) (by dsimp [upperBlocks]; omega)).apply hc'
  have habcd := run_comp habc hdRun
  have hdKeep := geometryFrame (keep := [7246, 2772, 1224, 1223]) (by decide)
    (by decide) ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) habcd
  have hd' : At d 3399
      [(7246, b32 tile), (2772, b32 stage.val), (1224, b32 key),
        (1223, maskSigned (-(query : Int)))] :=
    hdAt.mono ⟨(hdKeep _ (by decide)).trans ht.2.2.2.2.2.2.1,
      (hdKeep _ (by decide)).trans ht.2.2.2.2.2.2.2.1,
      (hdKeep _ (by decide)).trans ht.2.2.2.2.2.1,
      (hdKeep _ (by decide)).trans ht.2.2.2.2.1, trivial⟩
  obtain ⟨e, heRun, heAt⟩ := (singleStageLength l g key query tile stage hLen hKey hTile
    hUpper).apply hd'
  obtain ⟨f, hfRun, hfAt⟩ := (geometryBlockCeil 2 l g hEdge).apply
    (heAt.mono ⟨heAt.2.2.2.2.2.1, trivial⟩)
  have hfKeep := geometryFrame (keep := [2856]) (by decide) (by decide) ha'.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (run_comp (run_comp (run_comp (run_comp hbRun hcRun) hdRun) heRun) hfRun)
  have hf' : At f 3415 [(2856, b32 keyBlocks), (2878, b32 stageBlocks)] :=
    hfAt.mono ⟨(hfKeep _ (by decide)).trans ha.2.2.2.2.1, hfAt.2.2.2.2.1, trivial⟩
  obtain ⟨v, hvRun, hvAt⟩ := (minGeometryCount 1 l g keyBlocks stageBlocks
    (by dsimp [keyBlocks]; omega) (by dsimp [stageBlocks]; omega)).apply hf'
  have hDef : min keyBlocks upperBlocks = blocks := rfl
  have hvKeep := geometryFrame (keep := [1226]) (by decide) (by decide) hd'.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp (run_comp heRun hfRun) hvRun)
  have hv' : At v 3416 [(1226, b32 blocks), (2879, b32 clipped)] := by
    have hWord : d.regs 1226 = some (b32 blocks) := hDef ▸ hdAt.2.2.2.2.1
    exact hvAt.mono ⟨(hvKeep _ (by decide)).trans hWord, hvAt.2.2.2.2.1, trivial⟩
  obtain ⟨u, huRun, huAt⟩ := (firstBiasCapSegment l g blocks clipped hClipped hBound).apply hv'
  have hFull := run_comp
    (run_comp (run_comp (run_comp habcd heRun) hfRun) hvRun) huRun
  have huInputs := geometryFrame (keep := [1223, 1224]) (by decide) (by decide)
    ht.1 (by set_option maxRecDepth 100000 in kernel_rfl) hFull
  have huUpper := geometryFrame (keep := [1225]) (by decide) (by decide) hbAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (run_comp (run_comp (run_comp (run_comp (run_comp hcRun hdRun) heRun) hfRun) hvRun) huRun)
  have huBase := geometryFrame (keep := [2868]) (by decide) (by decide) heAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (run_comp (run_comp hfRun hvRun) huRun)
  have huBlocks := geometryFrame (keep := [1226]) (by decide) (by decide) hv'.1
    (by set_option maxRecDepth 100000 in kernel_rfl) huRun
  refine ⟨u, hFull, huAt.mono ⟨?_, ?_, ?_, ?_, ?_, huAt.2.2.2.2.1, trivial⟩⟩
  · exact (huInputs _ (by decide)).trans ht.2.2.2.2.1
  · exact (huInputs _ (by decide)).trans ht.2.2.2.2.2.1
  · exact (huBase _ (by decide)).trans heAt.2.2.2.2.1
  · exact (huUpper _ (by decide)).trans hbAt.2.2.2.2.1
  · exact (huBlocks _ (by decide)).trans hv'.2.2.2.2.1

/-- The synchronization addresses derived before the first request length reads. -/
def firstGeometrySync (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  [(2774, b32 (l.sharedBase+8*stage.val)), (2769, b32 (waitLoc l g stage 1).addr),
    (2788, b32 (scoreAddress l g stage 0))]

def firstGeometryAckFacts (p : Params) (l : Launch) (g batch tile : Nat) (stage : Fin 2) :
    List (Nat × Value) :=
  [(2767, b32 (waitLoc l g stage 0).addr), (2768, b32 1),
    (2769, b32 (waitLoc l g stage 1).addr), (2788, b32 (scoreAddress l g stage 0))] ++
    firstGeometryFacts p batch tile stage

theorem firstGeometryAckSetup (hp : Pre p l m) (g batch tile : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 2 3418
      (firstGeometrySync l g stage ++ firstGeometryFacts p batch tile stage)
      3420 (firstGeometryAckFacts p l g batch tile stage) := by
  have hBound := hp.shared.2.1
  have hStage := stage.isLt
  have hAddr : (waitLoc l g stage 0).addr = l.sharedBase + (192+8*stage.val) := rfl
  intro t ht
  simp only [firstGeometryAckFacts, firstGeometrySync, firstGeometryFacts,
    List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using norm_bits [hAddr]

theorem firstGeometryCountSetup (p : Params) (l : Launch)
    (g batch tile : Nat) (stage : Fin 2) (hb : 0 < Mma.trips p batch tile)
    (hb32 : Mma.trips p batch tile < 2^31) :
    Seg kernel Assumptions.all l g 2 3423 (firstGeometryAckFacts p l g batch tile stage)
      3425 ([(1229, b32 (Mma.trips p batch tile-1)), (2770, b32 0)] ++
        firstGeometryAckFacts p l g batch tile stage) := by
  intro t ht
  simp only [firstGeometryAckFacts, firstGeometryFacts, List.cons_append,
    List.nil_append] at ht ⊢
  seg_fp ht using norm_bits

/-- The launch addresses and lane predicates carried through the first length reads and
correction acknowledgement. -/
def firstGeometryCarryRegs : List Nat :=
  [2774, 2769, 2788, 2771, 2789, 5127, 481, 482, 1062, 2535, 2784, 2846, 2842, 2838,
    2834, 2830, 2826, 2822, 2818, 2814, 2810, 2806, 2802, 2798, 2794]

theorem geometryAckFrame {l : Launch} {g : Nat} {t u : TState} (tail : Bool)
    (hPc : t.pc = (if tail then 3423 else 3418))
    (hr : run kernel Assumptions.all l g 2 t = some u) :
    ∀ r ∈ firstGeometryCarryRegs, u.regs r = t.regs r := by
  let start : Nat := if tail then 3423 else 3418
  apply fixedFrame (first := start) (stop := start + 2)
    (kept := (· ∈ firstGeometryCarryRegs)) _ _ (by omega) (by omega) hr
  · intro pc hLo hHi
    cases tail <;> simp only [start, Bool.false_eq_true, ite_false, ite_true, Nat.reduceAdd]
      at hLo hHi <;> interval_cases pc
    · exact ⟨_, Flow.code_3418, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3419, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3423, rfl, rfl, fun _ => nofun, by decide⟩
    · exact ⟨_, Flow.code_3424, rfl, rfl, fun _ => nofun, by decide⟩
  · intro pc hLo hHi
    cases tail <;> simp [start] at hLo hHi <;>
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] <;> omega

/-- The first correction acknowledgement yields the real last-block counter and
phase-zero QK wait while retaining the fetched geometry and stable launch addresses. -/
theorem firstGeometryAckTraceFramed {X : Execution} (hp : Pre p l m) {g j batch tile : Nat}
    (stage : Fin 2) (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch) {t : TState}
    {F : List (Nat × Value)} (hF : ∀ x ∈ F, x.1 ∈ firstGeometryCarryRegs)
    (ht : At t 3418 ((firstGeometrySync l g stage ++ firstGeometryFacts p batch tile stage) ++ F))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ fails u, (X.tr g).drop j =
      List.replicate fails ⟨3420, .wait (waitLoc l g stage 0) 1 false true .cta⟩ ++
        ⟨3420, .wait (waitLoc l g stage 0) 1 true true .cta⟩ ::
          (X.tr g).drop (j+fails+1) ∧
      At u 3425 ([(1229, b32 (Mma.trips p batch tile-1)), (2770, b32 0)] ++
        firstGeometryAckFacts p l g batch tile stage ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+fails+1)) none := by
  obtain ⟨hOriginal, hCarry⟩ := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨v, hv, hvAt⟩ := (firstGeometryAckSetup hp g batch tile stage).apply (ht.mono hOriginal)
  have hCarryV := Epilogue.holdsSchedulerFrame hCarry (geometryAckFrame false ht.1 hv) hF
  have hvAt' := hvAt.mono ((holds_append ..).mpr ⟨hvAt.2.2.2.2, hCarryV⟩)
  have hBase : ((waitSite 0).base, b32 (waitLoc l g stage 0).addr) ∈
      firstGeometryAckFacts p l g batch tile stage := by simp [firstGeometryAckFacts, waitSite]
  have hPhase : ((waitSite 0).phase, b32 1) ∈
      firstGeometryAckFacts p l g batch tile stage := by simp [firstGeometryAckFacts, waitSite]
  have hFresh : ∀ x ∈ firstGeometryAckFacts p l g batch tile stage,
      x.1 ≠ (waitSite 0).result := by
    intro x hx
    simp only [firstGeometryAckFacts, firstGeometryFacts, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      change _ ≠ (9750 : Nat) <;> omega
  obtain ⟨failed, w, hEvents, hwAt, hwRun⟩ :=
    waitTraceAt hp stage 0 g 1 (by decide) (List.mem_append_left _ hBase)
      (List.mem_append_left _ hPhase) (fun x hx => by
        rcases List.mem_append.mp hx with h | h
        · exact hFresh x h
        · have hNe : (waitSite 0).result ∉ firstGeometryCarryRegs := by decide
          exact fun hEq => hNe (hEq ▸ hF x h)) hvAt'
      (hRun.after_local (run_rtg hv))
  have hTrips := Mma.trips_bounds hp hb hTile
  have hK := (hp.lengths batch hb).2.2
  obtain ⟨hAck, hCarryW⟩ := (holds_append ..).mp hwAt.2.2.2.2
  obtain ⟨u, hu, huAt⟩ :=
    (firstGeometryCountSetup p l g batch tile stage hTrips.1 (by omega)).apply (hwAt.mono hAck)
  have hCarryU := Epilogue.holdsSchedulerFrame hCarryW (geometryAckFrame true hwAt.1 hu) hF
  have hOut := huAt.mono ((holds_append ..).mpr ⟨huAt.2.2.2.2, hCarryU⟩)
  simpa only [List.append_assoc] using ⟨failed, u, hEvents, hOut, hwRun.after_local (run_rtg hu)⟩

/-- The fetched stage geometry meets the bounds of the subsequent mask and loop prelude. -/
theorem firstGeometryBounds (hp : Pre p l m) {batch tile lane : Nat} (stage : Fin 2)
    (hb : batch < p.batch) (hTile : 256*tile < p.qLength batch) (hLane : lane < 128) :
    let blocks := Mma.trips p batch tile
    let cap := blocks - stageGeometryBlocks p batch tile stage + 10
    let pastTile := p.kLength batch-p.qLength batch+256*tile
    0 < blocks ∧ blocks < 2^31 ∧ 0 < cap ∧ cap < 2^31 ∧
      pastTile+256 < 2^31 ∧ 128*(blocks-1) ≤ p.kLength batch ∧
      128*(2*tile+stage.val)+lane < p.qLength batch+256 := by
  have hTrips := Mma.trips_bounds hp hb hTile
  have hKey := (hp.lengths batch hb).2.2
  have hStage := stage.isLt
  dsimp only
  refine ⟨hTrips.1, ?_, by omega, ?_, ?_, ?_, ?_⟩
  all_goals omega

end PTX.Kernels.TmlFa4Fwd.Softmax
