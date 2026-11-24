-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaSelectionBallot
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinates
import Kernels.TmlFa4Fwd.Proof.MmaModel
import Kernels.TmlFa4Fwd.Flow.Code.Part032

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The four signed comparisons encode the cache thresholds for head groups. -/
private theorem mmaWidthThresholds (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) :
    Seg kernel [] l g 9 2064
      [(2503, b32 tiles), (7139, b32 heads), (2505, b32 work), (7156, b32 800),
       (7148, b32 batches), (7203, b32 b)] 2073
      [(364, .pred (decide (800 < 32 * tiles))), (365, .pred (decide (800 < 16 * tiles))),
       (366, .pred (decide (800 < 8 * tiles))), (367, .pred (decide (800 < 4 * tiles))),
       (2503, b32 tiles), (7139, b32 heads), (2505, b32 work),
       (7148, b32 batches), (7203, b32 b)] := by
  intro t ht
  have ht32 : tiles < 2 ^ 32 := by omega
  have hl32 : 256 * tiles < 2 ^ 32 := by omega
  have h32 : 32 * tiles < 2 ^ 31 := by omega
  have h16 : 16 * tiles < 2 ^ 31 := by omega
  have h8 : 8 * tiles < 2 ^ 31 := by omega
  have h4 : 4 * tiles < 2 ^ 31 := by omega
  have hs8 : (truncBits 32 (BitVec.ofInt 64 8)).toNat = 8 := rfl
  have hShift : BitVec.ofNat 64 tiles <<< 8 = BitVec.ofNat 64 (256 * tiles) := by
    rw [nf_shl]
    congr 1
    omega
  have s3 : min (truncBits 32 (BitVec.ofInt 64 3)).toNat 32 = 3 := rfl
  have s4 : min (truncBits 32 (BitVec.ofInt 64 4)).toNat 32 = 4 := rfl
  have s5 : min (truncBits 32 (BitVec.ofInt 64 5)).toNat 32 = 5 := rfl
  have s6 : min (truncBits 32 (BitVec.ofInt 64 6)).toNat 32 = 6 := rfl
  have hS800 : toSigned 32 (truncBits 32 (BitVec.ofNat 64 800)) = 800 := rfl
  have hd3 : (↑(256 * tiles) : Int) / 2 ^ 3 = (↑(32 * tiles) : Int) := by omega
  have hd4 : (↑(256 * tiles) : Int) / 2 ^ 4 = (↑(16 * tiles) : Int) := by omega
  have hd5 : (↑(256 * tiles) : Int) / 2 ^ 5 = (↑(8 * tiles) : Int) := by omega
  have hd6 : (↑(256 * tiles) : Int) / 2 ^ 6 = (↑(4 * tiles) : Int) := by omega
  seg_fp ht using
    simp only [hs8, ite_eq_right (show ¬8 ≥ 32 by decide), hShift,
      truncBits_ofNat ht32 (by decide), truncBits_ofNat hl32 (by decide), s3, s4, s5, s6,
      signedWord hTiles, hd3, hd4, hd5, hd6, BitVec.ofInt_natCast, hS800,
      truncBits_ofNat (show 32 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 16 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 8 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 4 * tiles < 2 ^ 32 by omega) (by decide),
      compare, Option.getD_some, signedWord h32, signedWord h16, signedWord h8, signedWord h4,
      gt_iff_lt, Value.pred.injEq, decide_eq_decide]
    all_goals omega

private def widthBits (p16 p8 p4 p2 : Bool) : Nat :=
  if p16 then
    if p8 then
      if p4 then (if p2 then 1 else 2) else 4
    else 8
  else 16

private abbrev coordinateArgs (tiles heads work batches b : Nat) : List (Nat × Value) :=
  [(2503, b32 tiles), (7139, b32 heads), (2505, b32 work),
   (7148, b32 batches), (7203, b32 b)]

private theorem mmaWidthSelectCode (l : Launch) (g : Nat) (p16 p8 p4 p2 : Bool)
    (tiles heads work batches b : Nat) :
    Seg kernel [] l g 4 2073
      ([(364, .pred p16), (365, .pred p8), (366, .pred p4), (367, .pred p2)] ++
        coordinateArgs tiles heads work batches b) 2077
      ((2514, b32 (widthBits p16 p8 p4 p2)) :: coordinateArgs tiles heads work batches b) := by
  cases p16 <;> cases p8 <;> cases p4 <;> cases p2 <;> intro t ht <;>
    simp only [coordinateArgs, List.cons_append, List.nil_append] at ht ⊢ <;> seg_fp ht using
      rfl

private abbrev cacheHeadCap (tiles : Nat) : Nat :=
  widthBits (decide (800 < 32 * tiles)) (decide (800 < 16 * tiles))
    (decide (800 < 8 * tiles)) (decide (800 < 4 * tiles))

private theorem capFits (tiles : Nat) : cacheHeadCap tiles ≤ 16 := by
  unfold cacheHeadCap widthBits
  split_ifs <;> decide

private theorem widthCap_eq (tiles heads : Nat) :
    min heads (cacheHeadCap tiles) = sectionWidth tiles heads := by
  unfold cacheHeadCap widthBits sectionWidth
  by_cases h16 : 800 < 32 * tiles <;> by_cases h8 : 800 < 16 * tiles <;>
    by_cases h4 : 800 < 8 * tiles <;> by_cases h2 : 800 < 4 * tiles <;>
    simp [h16, h8, h4, h2, Nat.not_le.mpr, Nat.le_of_not_lt]

/-- Clamp the decoded section width to the head count, then compute its tile span. -/
private theorem mmaChooseSectionWidth (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) (hHeads : heads < 2 ^ 31) :
    Seg kernel [] l g 6 2073
      ([(364, .pred (decide (800 < 32 * tiles))), (365, .pred (decide (800 < 16 * tiles))),
        (366, .pred (decide (800 < 8 * tiles))), (367, .pred (decide (800 < 4 * tiles)))] ++
        coordinateArgs tiles heads work batches b)
      2079 ([(2515, b32 (sectionWidth tiles heads)),
        (2516, b32 (sectionWidth tiles heads * tiles))] ++
        coordinateArgs tiles heads work batches b) := by
  let cap := cacheHeadCap tiles
  let width := min heads cap
  have hCap := capFits tiles
  have hWidth : width ≤ 16 := (Nat.min_le_right _ _).trans hCap
  have hSpan : width * tiles < 2 ^ 31 := by
    have hk := Nat.mul_le_mul_right tiles hWidth
    omega
  have hWidth_eq : width = sectionWidth tiles heads := widthCap_eq tiles heads
  rw [← hWidth_eq]
  have hRaw := mmaWidthSelectCode l g (decide (800 < 32 * tiles)) (decide (800 < 16 * tiles))
    (decide (800 < 8 * tiles)) (decide (800 < 4 * tiles)) tiles heads work batches b
  have hFinal : Seg kernel [] l g 2 2077
      ((2514, b32 cap) :: coordinateArgs tiles heads work batches b)
      2079 ([(2515, b32 width), (2516, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) := by
    intro t ht
    have hc : cap < 2 ^ 31 := by change cap ≤ 16 at hCap; omega
    have hc32 : cap < 2 ^ 32 := by omega
    have hh32 : heads < 2 ^ 32 := by omega
    have ht32 : tiles < 2 ^ 32 := by omega
    have hw32 : width < 2 ^ 32 := by omega
    have hs32 : width * tiles < 2 ^ 32 := by omega
    have hMin :
        (if (cap : Int) < (heads : Int) then BitVec.ofNat 64 cap else BitVec.ofNat 64 heads) =
          BitVec.ofNat 64 width := by
      by_cases h : cap < heads
      · simp [h, width, Nat.min_eq_right (Nat.le_of_lt h)]
      · simp [h, width, Nat.min_eq_left (Nat.le_of_not_lt h)]
    have hMinOp : (IntOp.min false == IntOp.max false) = false := rfl
    simp only [coordinateArgs, List.cons_append, List.nil_append] at ht ⊢
    seg_fp ht using
      simp only [b32, truncBits_ofNat hc32 (by decide), truncBits_ofNat hh32 (by decide),
        truncBits_ofNat ht32 (by decide), hMinOp, kind_s_beq_s, Bool.false_eq_true, ↓reduceIte,
        compare, signedWord hc, signedWord hHeads, decide_eq_true_eq, hMin,
        truncBits_ofNat hw32 (by decide), ← BitVec.ofNat_mul, truncBits_ofNat hs32 (by decide)]
  exact hRaw.comp hFinal

private theorem runUnsignedRangeDiv {l : Launch} {g pc dst rA rB a b : Nat}
    {t : TState} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some
      ⟨none, .int ⟨.div, .int .s 32, false, [some dst], [.reg rA, .reg rB]⟩⟩)
    (ht : At t pc F) (ha : t.regs rA = some (b32 a)) (hb : t.regs rB = some (b32 b))
    (ha31 : a < 2 ^ 31) (hb31 : b < 2 ^ 31) (hb0 : 0 < b) :
    run kernel [] l g 1 t = some (next (setReg t dst (b32 (a / b)))) := by
  have ha32 : a < 2 ^ 32 := by omega
  have hb32 : b < 2 ^ 32 := by omega
  have hq := Nat.div_le_self a b
  have hq32 : a / b < 2 ^ 32 := by omega
  have hBZero : b ≠ 0 := by omega
  have hANeg : ¬(a : Int) < 0 := by omega
  have hBNeg : ¬(b : Int) < 0 := by omega
  have hQOver : ¬2147483648 ≤ a / b := by omega
  apply run_local hc rfl ht
  rw [execLocalA_nil, execLocal_int rfl]
  simp [execInt, intResult, DType.width, DType.intLanes?, readBits, readReg, ha, hb,
    b32, truncBits_ofNat ha32 (by decide), truncBits_ofNat hb32 (by decide),
    intDiv, intOf, intBits, signedWord ha31, signedWord hb31, bind, Except.bind, pure, Except.pure,
    hBZero, hANeg, hBNeg, -Int.natCast_ediv, Int.ofNat_ediv_ofNat, hQOver,
    truncBits_ofNat hq32 (by decide)]

private theorem xorWord {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  have ha64 : a < 2 ^ 64 := by omega
  have hb64 : b < 2 ^ 64 := by omega
  have hx : a ^^^ b < 2 ^ 31 := Nat.xor_lt_two_pow ha hb
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_ofNat_lt ha64, toNat_ofNat_lt hb64,
    toNat_ofNat_lt (show a ^^^ b < 2 ^ 64 by omega)]

/-- Positive section division disables the code's adjustment for negative quotients. -/
private theorem mmaDivideHeadSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < 2 ^ 31) (hSpan : width * tiles < 2 ^ 31) (hSpan0 : 0 < width * tiles) :
    Seg kernel [] l g 6 2079
      ([(2515, b32 width), (2516, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) 2085
      ([(370, .pred false), (2517, b32 (work / (width * tiles))),
        (2515, b32 width), (2516, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let span := width * tiles
  let q := work / span
  let u := next (setReg t 2517 (b32 q))
  have ha : t.regs 2505 = some (b32 work) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs])
  have hb : t.regs 2516 = some (b32 span) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs, span])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_2079 ht ha hb hWork hSpan hSpan0
  have hu := ht.set (r := 2517) (v := b32 q) (by simp [coordinateArgs])
  have hXor : span ^^^ work < 2 ^ 31 := Nat.xor_lt_two_pow hSpan hWork
  have hWord := xorWord (a := span) (b := work) hSpan hWork
  have hXor32 : span ^^^ work < 2 ^ 32 := by omega
  have hWork32 : work < 2 ^ 32 := by omega
  have hSpan32 : span < 2 ^ 32 := by omega
  have hz : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hPos : ¬(↑(span ^^^ work) : Int) < 0 := by omega
  have hSteps : ∃ v, run kernel [] l g 5 u = some v ∧
      At v 2085 ([(370, .pred false), (2517, b32 q), (2515, b32 width), (2516, b32 span)] ++
        coordinateArgs tiles heads work batches b) := by
    change At u 2080
      ((2517, b32 q) :: [(2515, b32 width), (2516, b32 span)] ++
        coordinateArgs tiles heads work batches b) at hu
    simp only [coordinateArgs, List.cons_append, List.nil_append] at hu ⊢
    seg_fp hu using
      simp only [truncBits_ofNat hWork32 (by decide), truncBits_ofNat hSpan32 (by decide),
        hWord, truncBits_ofNat hXor32 (by decide), compare, Option.getD_some,
        signedWord hXor, hz, hPos, decide_false, Bool.and_false]
  obtain ⟨v, hTail, hv⟩ := hSteps
  exact ⟨v, run_comp hRun hTail, hv⟩

/-- Compute a section's relative index and choose whether it needs a shortened final stride. -/
private theorem mmaSectionOffsets (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < tiles * heads) (hItems : tiles * heads < 2 ^ 31)
    (hWidth : width ≤ 16) (hHeads : heads ≤ 2 ^ 25)
    (hSpan : width * tiles < 2 ^ 31) :
    Seg kernel [] l g 8 2085
      ([(370, .pred false), (2517, b32 (work / (width * tiles))),
        (2515, b32 width), (2516, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b)
      2093
      ([(2523, b32 (work % (width * tiles))), (2524, b32 (sectionHead tiles width work)),
        (2526, b32 (heads - sectionHead tiles width work)), (2515, b32 width),
        (371, .pred (decide (heads < sectionHead tiles width work + width)))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let start := sectionHead tiles width work
  let q := work / (width * tiles)
  let span := width * tiles
  have hStart : start < heads := sectionHead_lt hWork
  have hEnd : start + width < 2 ^ 31 := by omega
  have hHeads31 : heads < 2 ^ 31 := by omega
  have hSpan32 : span < 2 ^ 32 := by omega
  have hWork32 : work < 2 ^ 32 := by omega
  have hWidth32 : width < 2 ^ 32 := by omega
  have hHeads32 : heads < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hEnd32 : start + width < 2 ^ 32 := by omega
  have hQ32 : q < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self ..) hWork32
  have hProd := Nat.div_mul_le_self work span
  have hProd32 : q * span < 2 ^ 32 := lt_of_le_of_lt hProd hWork32
  have hMod : work - q * span = work % span := by
    have h := Nat.mod_add_div' work span
    change work % span + q * span = work at h
    omega
  have hMod32 : work % span < 2 ^ 32 := by
    have h := Nat.mod_le work span
    omega
  have hRemainder : heads - start < 2 ^ 32 := by omega
  have hz : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have hz32 : truncBits 32 0 = 0 := rfl
  have hQZero : BitVec.ofNat 64 q + 0 = BitVec.ofNat 64 q := BitVec.add_zero _
  have hHeadWord : q * width = start := rfl
  change At t 2085
    ([(370, .pred false), (2517, b32 q), (2515, b32 width), (2516, b32 span)] ++
      coordinateArgs tiles heads work batches b) at ht
  change ∃ u, run kernel [] l g 8 t = some u ∧
    At u 2093
      ([(2523, b32 (work % span)), (2524, b32 start), (2526, b32 (heads - start)),
        (2515, b32 width), (371, .pred (decide (heads < start + width)))] ++
        coordinateArgs tiles heads work batches b)
  simp only [coordinateArgs, List.cons_append, List.nil_append] at ht ⊢
  seg_fp ht using
    simp only [b32, hz, hz32, hQZero, truncBits_ofNat hQ32 (by decide),
      truncBits_ofNat hSpan32 (by decide), truncBits_ofNat hWork32 (by decide),
      truncBits_ofNat hWidth32 (by decide), truncBits_ofNat hHeads32 (by decide),
      ← BitVec.ofNat_add, ← BitVec.ofNat_mul, hHeadWord, truncBits_ofNat hProd32 (by decide),
      truncBits_ofNat hStart32 (by decide), truncBits_ofNat hEnd32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show q * span < 2 ^ 64 by omega) hProd,
      BitVec.ofNat_sub_ofNat_of_le _ _ (show start < 2 ^ 64 by omega) (Nat.le_of_lt hStart),
      hMod, truncBits_ofNat hMod32 (by decide), truncBits_ofNat hRemainder (by decide),
      compare, Option.getD_some, signedWord hEnd, signedWord hHeads31, gt_iff_lt, Int.ofNat_lt]

private theorem mmaTrimSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat} :
    Seg kernel [] l g 1 2093
      ([(2523, b32 (work % (width * tiles))), (2524, b32 (sectionHead tiles width work)),
        (2526, b32 (heads - sectionHead tiles width work)), (2515, b32 width),
        (371, .pred (decide (heads < sectionHead tiles width work + width)))] ++
        coordinateArgs tiles heads work batches b) 2094
      ([(2527, b32 (sectionStride tiles heads width work)),
        (2523, b32 (work % (width * tiles))), (2524, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  simp only [coordinateArgs, List.cons_append, List.nil_append] at ht ⊢
  by_cases h : heads < sectionHead tiles width work + width
  · simp only [decide_eq_true h] at ht
    have hm : heads - sectionHead tiles width work ≤ width := by omega
    seg_fp ht using simp only [sectionStride, Nat.min_eq_right hm]
  · simp only [decide_eq_false h] at ht
    have hm : width ≤ heads - sectionHead tiles width work := by omega
    seg_fp ht using simp only [sectionStride, Nat.min_eq_left hm]

/-- The positive division computes the tile from the end of the query section. -/
private theorem mmaReverseSectionTile (l : Launch) (g : Nat)
    {tiles heads work batches b width : Nat}
    (hTiles : tiles < 2 ^ 32)
    (hPos : work % (width * tiles) < 2 ^ 31)
    (hStride : sectionStride tiles heads width work < 2 ^ 31)
    (hStridePos : 0 < sectionStride tiles heads width work)
    (hQuotient : work % (width * tiles) / sectionStride tiles heads width work < tiles) :
    Seg kernel [] l g 9 2094
      ([(2527, b32 (sectionStride tiles heads width work)),
        (2523, b32 (work % (width * tiles))), (2524, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b)
      2103 ((2533, b32 (sectionCoords tiles heads width work).1) ::
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let pos := work % (width * tiles)
  let stride := sectionStride tiles heads width work
  let q := pos / stride
  let u := next (setReg t 2528 (b32 q))
  have hA : t.regs 2523 = some (b32 pos) := holds_mem ht.2.2.2.2 (by simp [pos])
  have hB : t.regs 2527 = some (b32 stride) := holds_mem ht.2.2.2.2 (by simp [stride])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_2094 ht hA hB hPos hStride hStridePos
  have hAt := ht.set (r := 2528) (v := b32 q) (by simp [coordinateArgs])
  have hXor : stride ^^^ pos < 2 ^ 31 := Nat.xor_lt_two_pow hStride hPos
  have hWord := xorWord (a := stride) (b := pos) hStride hPos
  have hXor32 : stride ^^^ pos < 2 ^ 32 := by omega
  have hQ : q < tiles := hQuotient
  have hQ32 : q < 2 ^ 32 := hQ.trans hTiles
  have hPos32 : pos < 2 ^ 32 := by omega
  have hStride32 : stride < 2 ^ 32 := by omega
  have hProduct : stride * q < 2 ^ 32 := by
    have hLe := Nat.div_mul_le_self pos stride
    rw [Nat.mul_comm] at hLe
    exact hLe.trans_lt hPos32
  have hZ : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hNonneg : (-1 : Int) < (↑(stride ^^^ pos) : Int) := by omega
  have hSub : tiles - q < 2 ^ 32 := (Nat.sub_le _ _).trans_lt hTiles
  have hMinus : BitVec.ofNat 64 tiles - BitVec.ofNat 64 q =
      BitVec.ofNat 64 (tiles - q) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (show q < 2 ^ 64 by omega) hQ.le
  have hPack : truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 4294967295 := rfl
  have hMask : truncBits 32 4294967295#64 = BitVec.ofNat 64 4294967295 := rfl
  have hTile : (sectionCoords tiles heads width work).1 = tiles - q - 1 := by
    simp [sectionCoords, sectionStride, sectionHead, pos, stride, q]
    omega
  have hNormalize : tiles - q + 4294967295 = 2 ^ 32 + (tiles - q - 1) := by omega
  have hEnd : truncBits 32 (BitVec.ofNat 64 (2 ^ 32 + (tiles - q - 1))) =
      BitVec.ofNat 64 (tiles - q - 1) := by
    simp only [truncBits, toNat_ofNat_lt (show 2 ^ 32 + (tiles - q - 1) < 2 ^ 64 by omega)]
    have hMod : (2 ^ 32 + (tiles - q - 1)) % 2 ^ 32 = tiles - q - 1 := by omega
    rw [hMod]
  let facts := (2528, b32 q) ::
    (2527, b32 stride) :: (2523, b32 pos) :: (2524, b32 (sectionHead tiles width work)) ::
    coordinateArgs tiles heads work batches b
  let adjusted := (374, .pred true) :: (2528, b32 q) ::
    coordinateArgs tiles heads work batches b
  have hComparison : Seg kernel [] l g 5 2095 facts 2100 adjusted := by
    intro w hw
    simp only [facts, adjusted, coordinateArgs] at hw ⊢
    seg_fp hw using
      simp only [truncBits_ofNat hQ32 (by decide), truncBits_ofNat hPos32 (by decide),
        truncBits_ofNat hStride32 (by decide), ← BitVec.ofNat_mul,
        truncBits_ofNat hProduct (by decide), hWord, truncBits_ofNat hXor32 (by decide),
        compare, Option.getD_some, signedWord hXor, hZ, hNonneg, decide_true, Bool.or_true]
  have hOffset : Seg kernel [] l g 3 2100 adjusted
      2103 ((2533, b32 (sectionCoords tiles heads width work).1) ::
        coordinateArgs tiles heads work batches b) := by
    intro w hw
    simp only [adjusted, coordinateArgs] at hw ⊢
    seg_fp hw using
      simp only [b32, truncBits_ofNat hQ32 (by decide), truncBits_ofNat hTiles (by decide),
        hMinus, truncBits_ofNat hSub (by decide), hPack, hMask, ← BitVec.ofNat_add, hNormalize,
        hTile, hEnd]
  obtain ⟨v, hv, hV⟩ := (hComparison.comp hOffset) u hAt
  exact ⟨v, run_comp hRun hv, hV⟩

private theorem sectionPos_lt {tiles heads width work : Nat}
    (hWork : work < tiles * heads) (hWidth : 0 < width) :
    work % (width * tiles) < sectionStride tiles heads width work * tiles := by
  let span := width * tiles
  let pos := work % span
  let start := sectionHead tiles width work
  have ht : 0 < tiles := Nat.pos_of_ne_zero fun h => by simp [h] at hWork
  have hJoin : pos + start * tiles = work := by
    simpa only [start, sectionHead, span, pos, Nat.mul_assoc] using Nat.mod_add_div' work span
  change pos < min width (heads - start) * tiles
  by_cases h : width ≤ heads - start
  · rw [Nat.min_eq_left h]
    exact Nat.mod_lt _ (Nat.mul_pos hWidth ht)
  · rw [Nat.min_eq_right (by omega)]
    have hHead := sectionHead_lt (width := width) hWork
    change start < heads at hHead
    have he : heads - start + start = heads := by omega
    have hh := congrArg (fun n => n * tiles) he
    rw [Nat.add_mul, Nat.mul_comm heads] at hh
    omega

private theorem headsFitSections {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    p.heads ≤ 2 ^ 25 := by
  have hO := hp.ranges p.oRegion (by simp)
  change p.oBase + 512 * p.heads * p.totalQ ≤ 2 ^ 64 at hO
  have hr := hp.raggedBase
  rw [← Nat.mul_assoc] at hr
  omega


/-- The MMA address arithmetic computes the selected request's actual reverse tile. -/
theorem computeSelectedMmaTile {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch item start previous : Nat}
    (hBatch : batch < p.batch) (hPrefix : start + previous = tilePrefix p batch * p.heads)
    (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 41 2062
      [(1186, b32 start), (7201, b32 previous), (1072, b32 item),
        (2503, b32 (requestTiles p batch)), (7139, b32 p.heads), (7156, b32 800),
        (7148, b32 p.batch), (7203, b32 batch)]
      2103 [(2533, b32 (assignedCoordinates p batch item).1),
        (7203, b32 batch), (7148, b32 p.batch)] := by
  let tiles := requestTiles p batch
  let width := sectionWidth tiles p.heads
  let work := item - (start + previous)
  let pos := sectionCoords tiles p.heads width work
  have hPos : pos = assignedCoordinates p batch item := by simp only [pos, tiles, work, width,
    assignedCoordinates, hPrefix]
  have hPrefixBounds := hp.prefixWork_signed (show batch + 1 ≤ p.batch by omega)
  have hItems : tiles * p.heads < 2 ^ 31 := by
    rw [tilePrefix_succ, Nat.add_mul] at hPrefixBounds
    exact lt_of_le_of_lt (Nat.le_add_left _ _) hPrefixBounds
  have hItem : item < 2 ^ 31 := hHi.trans hPrefixBounds
  have hStart : start + previous ≤ item := hPrefix.symm ▸ hLo
  have hEnd : item < start + previous + tiles * p.heads := by
    simpa only [tilePrefix_succ, Nat.add_mul, ← hPrefix, tiles] using hHi
  have hWork : work < tiles * p.heads := by
    change item - (start + previous) < tiles * p.heads
    omega
  have hWork31 : work < 2 ^ 31 := hWork.trans hItems
  have hTiles : 256 * tiles < 2 ^ 31 := by
    have hLen := hp.qLength_fits hBatch
    have hMul := requestTiles_mul_le p batch
    rw [Nat.mul_comm] at hMul
    omega
  have hHeads := hp.heads_signed
  have hHeadPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTilesPos : 0 < tiles := Nat.pos_of_ne_zero fun he => by simp [he] at hWork
  have hWidth : 0 < width := sectionWidth_pos hHeadPos
  have hWidth16 : width ≤ 16 := by
    rw [show width = _ from (widthCap_eq tiles p.heads).symm]
    exact (Nat.min_le_right _ _).trans (capFits tiles)
  have hLimit : width ≤ p.heads := by
    rw [show width = _ from (widthCap_eq tiles p.heads).symm]
    exact Nat.min_le_left _ _
  have hSpan : width * tiles < 2 ^ 31 := by
    rw [Nat.mul_comm]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left tiles hLimit) hItems
  have hSpanPos : 0 < width * tiles := Nat.mul_pos hWidth hTilesPos
  have hFirst := sectionHead_lt (width := width) hWork
  have hStride : sectionStride tiles p.heads width work < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.min_le_left _ _) (lt_of_le_of_lt hWidth16 (by decide))
  have hStridePos : 0 < sectionStride tiles p.heads width work :=
    Nat.lt_min.mpr ⟨hWidth, by omega⟩
  have hRelative : work % (width * tiles) < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.mod_le _ _) hWork31
  have hQ : work % (width * tiles) / sectionStride tiles p.heads width work < tiles :=
    (Nat.div_lt_iff_lt_mul hStridePos).2
      (by simpa only [Nat.mul_comm] using sectionPos_lt hWork hWidth)
  have hTile32 : tiles < 2 ^ 32 := by omega
  let input := [(1186, b32 start), (7201, b32 previous), (1072, b32 item),
    (2503, b32 tiles), (7139, b32 p.heads), (7156, b32 800), (7148, b32 p.batch),
    (7203, b32 batch)]
  have hKeep : ((kernel.code.drop 2062).take 2).all
      (fun ins => [2503, 7139, 7156, 7148, 7203].all
        (fun r => !(writesRegs ins.op).contains r)) = true := by decide +kernel
  have hRel : Seg kernel [] l g 2 2062 input 2064
      ((2503, b32 tiles) :: (7139, b32 p.heads) :: (2505, b32 work) ::
        (7156, b32 800) :: [(7148, b32 p.batch), (7203, b32 batch)]) := by
    intro t ht
    obtain ⟨u, hRun, hu⟩ := selectedRelativeItem l g hStart hItem t
      (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, trivial⟩)
    have hr (r : Nat) (hm : r ∈ [2503, 7139, 7156, 7148, 7203]) : u.regs r = t.regs r :=
      schedulerLocalFrame hKeep (by decide +kernel) hRun ht.1.ge (by rw [ht.1]) hm
    exact ⟨u, hRun, hu.mono
      ⟨(hr _ (by simp)).trans (holds_lookup ht.2.2.2.2 rfl),
       (hr _ (by simp)).trans (holds_lookup ht.2.2.2.2 rfl), hu.2.2.2.2.1,
       (hr _ (by simp)).trans (holds_lookup ht.2.2.2.2 rfl),
       (hr _ (by simp)).trans (holds_lookup ht.2.2.2.2 rfl),
       (hr _ (by simp)).trans (holds_lookup ht.2.2.2.2 rfl), trivial⟩⟩
  have hCalc := hRel.comp
    ((mmaWidthThresholds l g hTiles).comp
    ((mmaChooseSectionWidth l g hTiles hHeads).comp
    ((mmaDivideHeadSection l g hWork31 hSpan hSpanPos).comp
    ((mmaSectionOffsets l g hWork hItems hWidth16 (headsFitSections hp) hSpan).comp
    ((mmaTrimSection l g).comp (mmaReverseSectionTile l g hTile32 hRelative hStride
      hStridePos hQ))))))
  intro t ht
  obtain ⟨u, hRun, hAt⟩ := hCalc t ht
  exact ⟨u, hRun, hAt.mono
    ⟨hPos ▸ hAt.2.2.2.2.1, holds_lookup hAt.2.2.2.2 rfl,
      holds_lookup hAt.2.2.2.2 rfl, trivial⟩⟩

/-- The selected MMA tile enters the real request-metadata sequence with its launch pointers. -/
theorem selectedMmaTileEntry {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch item start previous : Nat}
    (hBatch : batch < p.batch) (hPrefix : start + previous = tilePrefix p batch * p.heads)
    (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel Assumptions.all l g 47 2062
      ([(1186, b32 start), (7201, b32 previous), (1072, b32 item),
        (2503, b32 (requestTiles p batch)), (7139, b32 p.heads), (7156, b32 800),
        (7148, b32 p.batch), (7203, b32 batch)] ++
       [(7502, b64 p.cuQBase), (7503, b64 p.usedKBase), (2535, b32 l.sharedBase)])
      2109 [(7203, b32 batch), (7502, b64 p.cuQBase), (7503, b64 p.usedKBase),
        (7202, b32 (256 * ((assignedCoordinates p batch item).1 + 1))),
        (2535, b32 l.sharedBase)] := by
  intro t ht
  obtain ⟨u, hr, hu⟩ := computeSelectedMmaTile hp g hBatch hPrefix hLo hHi t
    (ht.mono ((holds_append ..).mp ht.2.2.2.2).1)
  have hFrame (r : Nat) (hm : r ∈ [2535, 7203, 7502, 7503]) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 2062) (len := 41) (by decide +kernel) (by decide +kernel)
      hr ht.1.ge (by rw [ht.1]) hm
  have hShared : t.regs 2535 = some (b32 l.sharedBase) := holds_lookup ht.2.2.2.2 rfl
  obtain ⟨v, hv, hV⟩ := selectedTileEnter hp g hBatch (assignedCoordinates_valid hp hLo hHi).1 u
    (hu.mono ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.2.2.1, hu.2.2.2.2.1,
      (hFrame _ (by decide)).trans hShared, trivial⟩)
  have hTotal := run_comp hr hv
  have hStraight : ((kernel.code.drop 2062).take (47 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := by decide +kernel
  have hSaved (r : Nat) (hm : r ∈ [2535, 7203, 7502, 7503]) : v.regs r = t.regs r :=
    schedulerLocalFrame (lo := 2062) (len := 47) (by decide +kernel) hStraight
      hTotal ht.1.ge (by rw [ht.1]) hm
  exact ⟨v, localRun (by decide) (by decide) ht.1 hStraight hTotal, hV.mono
    ⟨(hSaved _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hSaved _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      (hSaved _ (by decide)).trans (holds_lookup ht.2.2.2.2 rfl),
      hV.2.2.2.2.1, (hSaved _ (by decide)).trans hShared, trivial⟩⟩

end PTX.Kernels.TmlFa4Fwd.Mma
