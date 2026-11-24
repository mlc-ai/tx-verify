-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinates
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScheduleTileInputs
import Kernels.TmlFa4Fwd.Flow.Code.Part050
import Kernels.TmlFa4Fwd.Flow.Code.Part051

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem scanSignedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

/-- The four signed comparisons encode the cache thresholds for head groups. -/
private theorem widthThresholds (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) :
    Seg kernel [] l g 9 3234
      [(2730, b32 tiles), (7140, b32 heads), (2732, b32 work), (7157, b32 800),
       (7150, b32 batches), (7247, b32 b)] 3243
      [(468, .pred (decide (800 < 32 * tiles))), (469, .pred (decide (800 < 16 * tiles))),
       (470, .pred (decide (800 < 8 * tiles))), (471, .pred (decide (800 < 4 * tiles))),
       (2730, b32 tiles), (7140, b32 heads), (2732, b32 work),
       (7150, b32 batches), (7247, b32 b)] := by
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
      scanSignedWord hTiles, hd3, hd4, hd5, hd6, BitVec.ofInt_natCast, hS800,
      truncBits_ofNat (show 32 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 16 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 8 * tiles < 2 ^ 32 by omega) (by decide),
      truncBits_ofNat (show 4 * tiles < 2 ^ 32 by omega) (by decide),
      compare, Option.getD_some, scanSignedWord h32, scanSignedWord h16,
      scanSignedWord h8, scanSignedWord h4,
      gt_iff_lt, Value.pred.injEq, decide_eq_decide]
    all_goals omega

private def widthBits (p16 p8 p4 p2 : Bool) : Nat :=
  if p16 then
    if p8 then
      if p4 then (if p2 then 1 else 2) else 4
    else 8
  else 16

private abbrev coordinateArgs (tiles heads work batches b : Nat) : List (Nat × Value) :=
  [(2730, b32 tiles), (7140, b32 heads), (2732, b32 work),
   (7150, b32 batches), (7247, b32 b)]

private theorem widthSelectCode (l : Launch) (g : Nat) (p16 p8 p4 p2 : Bool)
    (tiles heads work batches b : Nat)
    (h8 : p8 = true → p16 = true) (h4 : p4 = true → p8 = true)
    (h2 : p2 = true → p4 = true) :
    Seg kernel [] l g 4 3243
      ([(468, .pred p16), (469, .pred p8), (470, .pred p4), (471, .pred p2)] ++
        coordinateArgs tiles heads work batches b) 3247
      ((2741, b32 (widthBits p16 p8 p4 p2)) :: coordinateArgs tiles heads work batches b) := by
  cases p16 <;> cases p8 <;> cases p4 <;> cases p2 <;> simp at h8 h4 h2
  all_goals
    intro t ht
    simp only [coordinateArgs, List.cons_append, List.nil_append] at ht ⊢
    seg_fp ht using rfl

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
private theorem chooseSectionWidth (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) (hHeads : heads < 2 ^ 31) :
    Seg kernel [] l g 6 3243
      ([(468, .pred (decide (800 < 32 * tiles))), (469, .pred (decide (800 < 16 * tiles))),
        (470, .pred (decide (800 < 8 * tiles))), (471, .pred (decide (800 < 4 * tiles)))] ++
        coordinateArgs tiles heads work batches b)
      3249 ([(2742, b32 (sectionWidth tiles heads)),
        (2743, b32 (sectionWidth tiles heads * tiles))] ++
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
  have hRaw := widthSelectCode l g (decide (800 < 32 * tiles)) (decide (800 < 16 * tiles))
    (decide (800 < 8 * tiles)) (decide (800 < 4 * tiles)) tiles heads work batches b
    (by simp only [decide_eq_true_eq]; omega) (by simp only [decide_eq_true_eq]; omega)
    (by simp only [decide_eq_true_eq]; omega)
  have hFinal : Seg kernel [] l g 2 3247
      ((2741, b32 cap) :: coordinateArgs tiles heads work batches b)
      3249 ([(2742, b32 width), (2743, b32 (width * tiles))] ++
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
        compare, scanSignedWord hc, scanSignedWord hHeads, decide_eq_true_eq, hMin,
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
    intDiv, intOf, intBits, scanSignedWord ha31, scanSignedWord hb31,
    bind, Except.bind, pure, Except.pure,
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
private theorem divideHeadSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < 2 ^ 31) (hSpan : width * tiles < 2 ^ 31) (hSpan0 : 0 < width * tiles) :
    Seg kernel [] l g 6 3249
      ([(2742, b32 width), (2743, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) 3255
      ([(474, .pred false), (2744, b32 (work / (width * tiles))),
        (2742, b32 width), (2743, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let span := width * tiles
  let q := work / span
  let u := next (setReg t 2744 (b32 q))
  have ha : t.regs 2732 = some (b32 work) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs])
  have hb : t.regs 2743 = some (b32 span) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs, span])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_3249 ht ha hb hWork hSpan hSpan0
  have hu := ht.set (r := 2744) (v := b32 q) (by simp [coordinateArgs])
  have hXor : span ^^^ work < 2 ^ 31 := Nat.xor_lt_two_pow hSpan hWork
  have hWord := xorWord (a := span) (b := work) hSpan hWork
  have hXor32 : span ^^^ work < 2 ^ 32 := by omega
  have hWork32 : work < 2 ^ 32 := by omega
  have hSpan32 : span < 2 ^ 32 := by omega
  have hz : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hPos : ¬(↑(span ^^^ work) : Int) < 0 := by omega
  have hSteps : ∃ v, run kernel [] l g 5 u = some v ∧
      At v 3255 ([(474, .pred false), (2744, b32 q), (2742, b32 width), (2743, b32 span)] ++
        coordinateArgs tiles heads work batches b) := by
    change At u 3250
      ((2744, b32 q) :: [(2742, b32 width), (2743, b32 span)] ++
        coordinateArgs tiles heads work batches b) at hu
    simp only [coordinateArgs, List.cons_append, List.nil_append] at hu ⊢
    seg_fp hu using
      simp only [truncBits_ofNat hWork32 (by decide), truncBits_ofNat hSpan32 (by decide),
        hWord, truncBits_ofNat hXor32 (by decide), compare, Option.getD_some,
        scanSignedWord hXor, hz, hPos, decide_false, Bool.and_false]
  obtain ⟨v, hTail, hv⟩ := hSteps
  exact ⟨v, run_comp hRun hTail, hv⟩

private theorem sectionOffsets (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < tiles * heads) (hItems : tiles * heads < 2 ^ 31)
    (hWidth : width ≤ 16) (hHeads : heads ≤ 2 ^ 25)
    (hSpan : width * tiles < 2 ^ 31) :
    Seg kernel [] l g 8 3255
      ([(474, .pred false), (2744, b32 (work / (width * tiles))),
        (2742, b32 width), (2743, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b)
      3263
      ([(2750, b32 (work % (width * tiles))), (2751, b32 (sectionHead tiles width work)),
        (2753, b32 (heads - sectionHead tiles width work)), (2742, b32 width),
        (475, .pred (decide (heads < sectionHead tiles width work + width)))] ++
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
  change At t 3255
    ([(474, .pred false), (2744, b32 q), (2742, b32 width), (2743, b32 span)] ++
      coordinateArgs tiles heads work batches b) at ht
  change ∃ u, run kernel [] l g 8 t = some u ∧
    At u 3263
      ([(2750, b32 (work % span)), (2751, b32 start), (2753, b32 (heads - start)),
        (2742, b32 width), (475, .pred (decide (heads < start + width)))] ++
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
      compare, Option.getD_some, scanSignedWord hEnd, scanSignedWord hHeads31,
      gt_iff_lt, Int.ofNat_lt]

private theorem trimSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat} :
    Seg kernel [] l g 1 3263
      ([(2750, b32 (work % (width * tiles))), (2751, b32 (sectionHead tiles width work)),
        (2753, b32 (heads - sectionHead tiles width work)), (2742, b32 width),
        (475, .pred (decide (heads < sectionHead tiles width work + width)))] ++
        coordinateArgs tiles heads work batches b) 3264
      ([(2754, b32 (sectionStride tiles heads width work)),
        (2750, b32 (work % (width * tiles))), (2751, b32 (sectionHead tiles width work))] ++
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

/-- Divide the within-section index, preserving the code's unadjusted quotient in the
nonnegative case. -/
private theorem divideSectionTile (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hPos : work % (width * tiles) < 2 ^ 31)
    (hStride : sectionStride tiles heads width work < 2 ^ 31)
    (hStride0 : 0 < sectionStride tiles heads width work) :
    Seg kernel [] l g 6 3264
      ([(2754, b32 (sectionStride tiles heads width work)),
        (2750, b32 (work % (width * tiles))), (2751, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) 3270
      ([(478, .pred true),
        (2755, b32 (work % (width * tiles) / sectionStride tiles heads width work)),
        (2754, b32 (sectionStride tiles heads width work)),
        (2750, b32 (work % (width * tiles))), (2751, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let pos := work % (width * tiles)
  let stride := sectionStride tiles heads width work
  let first := sectionHead tiles width work
  let q := pos / stride
  let u := next (setReg t 2755 (b32 q))
  have ha : t.regs 2750 = some (b32 pos) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs, pos])
  have hb : t.regs 2754 = some (b32 stride) :=
    holds_mem ht.2.2.2.2 (by simp [coordinateArgs, stride])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_3264 ht ha hb hPos hStride hStride0
  have hu := ht.set (r := 2755) (v := b32 q) (by simp [coordinateArgs])
  have hXor : stride ^^^ pos < 2 ^ 31 := Nat.xor_lt_two_pow hStride hPos
  have hWord := xorWord (a := stride) (b := pos) hStride hPos
  have hXor32 : stride ^^^ pos < 2 ^ 32 := by omega
  have hPos32 : pos < 2 ^ 32 := by omega
  have hStride32 : stride < 2 ^ 32 := by omega
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hNonneg : (-1 : Int) < ↑(stride ^^^ pos) := by omega
  have hSteps : ∃ v, run kernel [] l g 5 u = some v ∧
      At v 3270
        ([(478, .pred true), (2755, b32 q), (2754, b32 stride), (2750, b32 pos),
          (2751, b32 first)] ++ coordinateArgs tiles heads work batches b) := by
    change At u 3265
      ((2755, b32 q) :: [(2754, b32 stride), (2750, b32 pos), (2751, b32 first)] ++
        coordinateArgs tiles heads work batches b) at hu
    simp only [coordinateArgs, List.cons_append, List.nil_append] at hu ⊢
    seg_fp hu using
      simp only [truncBits_ofNat hPos32 (by decide), truncBits_ofNat hStride32 (by decide),
        hWord, truncBits_ofNat hXor32 (by decide), compare, Option.getD_some,
        scanSignedWord hXor, hNeg, gt_iff_lt, hNonneg, decide_true, Bool.or_true]
  obtain ⟨v, hTail, hv⟩ := hSteps
  exact ⟨v, run_comp hRun hTail, hv⟩

private theorem headsFitSections {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    p.heads ≤ 2 ^ 25 := by
  have hO := hp.ranges p.oRegion (by simp)
  change p.oBase + 512 * p.heads * p.totalQ ≤ 2 ^ 64 at hO
  have hr := hp.raggedBase
  rw [← Nat.mul_assoc] at hr
  omega

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

private theorem writeReverseTile (l : Launch) (g : Nat) {tiles heads work batches batch width : Nat}
    (hTiles : tiles < 2^32) (hBack : work % (width*tiles) / sectionStride tiles heads width work <
      tiles) (hBatches : batches < 2^31) (hBatch : batch < batches) :
    Seg kernel [] l g 4 3270
      ([(478,.pred true),
        (2755,b32 (work % (width*tiles) / sectionStride tiles heads width work)),
        (2754,b32 (sectionStride tiles heads width work)),
        (2750,b32 (work % (width*tiles))),
        (2751,b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches batch)
      3274 [(7247,b32 batch), (7246,b32 (sectionCoords tiles heads width work).1),
        (783,.pred true)] := by
  let back := work % (width*tiles) / sectionStride tiles heads width work
  have hBackLT : back < tiles := hBack
  have hBack32 : back < 2^32 := hBackLT.trans hTiles
  have hDiff32 : tiles-back < 2^32 := (Nat.sub_le ..).trans_lt hTiles
  have hTile32 : tiles-1-back < 2^32 :=
    (le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)).trans_lt hTiles
  have hWiden : 2^32 + (tiles-1-back) < 2^64 := by omega
  have hSub : truncBits 32 (BitVec.ofNat 64 tiles - BitVec.ofNat 64 back) =
      BitVec.ofNat 64 (tiles-back) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (show back < 2^64 by omega) hBackLT.le,
      truncBits_ofNat hDiff32 (by decide)]
  have hNeg : truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 4294967295 := rfl
  have hReduce : tiles-back + 4294967295 = 2^32 + (tiles-1-back) := by omega
  have hTile : truncBits 32 (BitVec.ofNat 64 (tiles-back) + BitVec.ofNat 64 4294967295) =
      BitVec.ofNat 64 (tiles-1-back) := by
    rw [← BitVec.ofNat_add, hReduce, truncBits,
      toNat_ofNat_lt hWiden, Nat.add_mod,
      Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hTile32]
  intro t ht
  change At t 3270 ([(478,.pred true), (2755,b32 back),
    (2754,b32 (sectionStride tiles heads width work)), (2750,b32 (work % (width*tiles))),
    (2751,b32 (sectionHead tiles width work))] ++
      coordinateArgs tiles heads work batches batch) at ht
  simp only [coordinateArgs, List.cons_append, List.nil_append] at ht
  change ∃ u, run kernel [] l g 4 t = some u ∧
    At u 3274 [(7247,b32 batch), (7246,b32 (tiles-1-back)), (783,.pred true)]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hTiles (by decide),
      truncBits_ofNat hBack32 (by decide), hNeg, hSub,
      truncBits_ofNat hDiff32 (by decide),
      truncBits_ofNat (show 4294967295 < 2^32 by decide) (by decide), hTile,
      truncBits_ofNat (show batch < 2^32 by omega) (by decide),
      truncBits_ofNat (show batches < 2^32 by omega) (by decide),
      compare, Option.getD_some, scanSignedWord (hBatch.trans hBatches), scanSignedWord hBatches,
      Int.ofNat_lt, hBatch, decide_true]

/-- The softmax coordinate segment computes the scheduler's assigned query tile. -/
theorem selectedTileSegment {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch item : Nat} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    Seg kernel [] l g 40 3234
      [(2730,b32 (requestTiles p batch)), (7140,b32 p.heads),
       (2732,b32 (item-tilePrefix p batch * p.heads)), (7157,b32 800),
       (7150,b32 p.batch), (7247,b32 batch)] 3274
      [(7247,b32 batch), (7246,b32 (assignedCoordinates p batch item).1), (783,.pred true)] := by
  let tiles := requestTiles p batch
  let width := sectionWidth tiles p.heads
  let work := item - tilePrefix p batch * p.heads
  have hPrefixBounds := hp.prefixWork_signed (show batch+1 ≤ p.batch by omega)
  have hItems : tiles * p.heads < 2^31 := by
    rw [tilePrefix_succ, Nat.add_mul] at hPrefixBounds
    exact lt_of_le_of_lt (Nat.le_add_left _ _) hPrefixBounds
  have hEnd : item < tilePrefix p batch * p.heads + tiles * p.heads := by
    simpa only [tilePrefix_succ, Nat.add_mul, tiles] using hHi
  have hWork : work < tiles * p.heads := by dsimp [work]; omega
  have hWork31 : work < 2^31 := hWork.trans hItems
  have hTiles : 256 * tiles < 2^31 := by
    have hLen := hp.qLength_fits hBatch
    have hMul := requestTiles_mul_le p batch
    rw [Nat.mul_comm] at hMul
    omega
  have hHeads := hp.heads_signed
  have hHeadPos : 0 < p.heads := by unfold Params.heads; have := hp.shape.2.2.1; omega
  have hTilesPos : 0 < tiles := Nat.pos_of_ne_zero fun h => by simp [h] at hWork
  have hWidth : 0 < width := sectionWidth_pos hHeadPos
  have hWidth16 : width ≤ 16 := by
    rw [show width = _ from (widthCap_eq tiles p.heads).symm]
    exact (Nat.min_le_right _ _).trans (capFits tiles)
  have hLimit : width ≤ p.heads := by
    rw [show width = _ from (widthCap_eq tiles p.heads).symm]
    exact Nat.min_le_left _ _
  have hSpan : width * tiles < 2^31 := by
    rw [Nat.mul_comm]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left tiles hLimit) hItems
  have hSpanPos : 0 < width * tiles := Nat.mul_pos hWidth hTilesPos
  have hFirst := sectionHead_lt (width := width) hWork
  have hStride : sectionStride tiles p.heads width work < 2^31 :=
    lt_of_le_of_lt (Nat.min_le_left _ _) (lt_of_le_of_lt hWidth16 (by decide))
  have hStridePos : 0 < sectionStride tiles p.heads width work :=
    Nat.lt_min.mpr ⟨hWidth, by omega⟩
  have hRelative : work % (width * tiles) < 2^31 := lt_of_le_of_lt (Nat.mod_le _ _) hWork31
  have hBack := (Nat.div_lt_iff_lt_mul hStridePos).mpr (by
    rw [Nat.mul_comm]
    exact sectionPos_lt hWork hWidth)
  exact (widthThresholds l g hTiles).comp
    ((chooseSectionWidth l g hTiles hHeads).comp
    ((divideHeadSection l g hWork31 hSpan hSpanPos).comp
    ((sectionOffsets l g hWork hItems hWidth16 (headsFitSections hp) hSpan).comp
    ((trimSection l g).comp
    ((divideSectionTile l g hRelative hStride hStridePos).comp
      (writeReverseTile l g (by omega) hBack hp.shape.2.1 hBatch))))))

private theorem coordinateCoreSlice :
    ((kernel.code.drop 3234).take 40).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem coordinateOut {l : Launch} {g : Nat} {t : TState}
    (hLo : 3234 ≤ t.pc) (hHi : t.pc < 3274) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hm : ins ∈ (kernel.code.drop 3234).take 40 := by
      apply List.mem_of_getElem? (i := t.pc - 3234)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
      exact hc
    apply Assumptions.out_all_eq_nil _ _ _ hc (List.all_eq_true.mp coordinateCoreSlice _ hm)
    all_goals
      simp only [Assumptions.swExp2Sites, Assumptions.tcLdDataflowSites,
        Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

/-- The chosen batch and tile survive in the physical softmax register state. -/
def firstActiveTileFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8) (batch : Nat) :
    List (Nat × Value) :=
  [(7247,b32 batch), (7246,b32 (assignedCoordinates p batch (g/l.block)).1), (783,.pred true)] ++
    dispatchInput p l warp

/-- The common selected-coordinate segment retains the ABI needed by the softmax body. -/
theorem selectedTileWithDispatch {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {thread g batch : Nat} {warp : Fin 8} {t : TState} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hArgs : At t 3234
      [(2730, b32 (requestTiles p batch)), (7140, b32 p.heads),
       (2732, b32 (g / l.block - tilePrefix p batch * p.heads)), (7157, b32 800),
       (7150, b32 p.batch), (7247, b32 batch)])
    (hCarry : Holds t.regs (dispatchInput p l warp)) :
    ∃ u, run kernel Assumptions.all l thread 40 t = some u ∧
      At u 3274 (firstActiveTileFacts p l g warp batch) := by
  obtain ⟨u, hu, hU⟩ := (selectedTileSegment hp thread hb hLo hHi).apply hArgs
  have hStraight : ((kernel.code.drop 3234).take (40 - 1)).all
      (fun i => schedulerFallsThrough i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hAll := schedulerLocalTransport (lo := 3234) (len := 40) hStraight
    (fun h0 h1 => coordinateOut h0 h1) hu hArgs.1.ge (by rw [hArgs.1])
  have hKeep : ((kernel.code.drop 3234).take 40).all
      (fun i => ((dispatchInput p l warp).map Prod.fst).all
        (fun r => !(writesRegs i.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hFrame (r : Nat) (hr : r ∈ (dispatchInput p l warp).map Prod.fst) :
      u.regs r = t.regs r :=
    schedulerLocalFrame (lo := 3234) (len := 40) hKeep hStraight hu
      hArgs.1.ge (by rw [hArgs.1]) hr
  have hSaved := holdsSchedulerFrame hCarry hFrame (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, hAll, hU.mono
    ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hSaved⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
