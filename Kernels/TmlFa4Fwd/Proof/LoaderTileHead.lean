-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSelectedCoordinates
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinates
public import Kernels.TmlFa4Fwd.Flow.Code.Part005
public import Lemmas.Flow.Scalars

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

private theorem signedWord {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

/-- The four signed comparisons encode the cache thresholds for head groups. -/
private theorem widthThresholds (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) :
    Seg kernel [] l g 9 311
      [(1754, b32 tiles), (7136, b32 heads), (1756, b32 work), (7154, b32 800),
       (7144, b32 batches), (7170, b32 b)] 320
      [(91, .pred (decide (800 < 32 * tiles))), (92, .pred (decide (800 < 16 * tiles))),
       (93, .pred (decide (800 < 8 * tiles))), (94, .pred (decide (800 < 4 * tiles))),
       (1754, b32 tiles), (7136, b32 heads), (1756, b32 work),
       (7144, b32 batches), (7170, b32 b)] := by
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
  [(1754, b32 tiles), (7136, b32 heads), (1756, b32 work),
   (7144, b32 batches), (7170, b32 b)]

private theorem widthSelectCode (l : Launch) (g : Nat) (p16 p8 p4 p2 : Bool)
    (tiles heads work batches b : Nat) :
    Seg kernel [] l g 4 320
      ([(91, .pred p16), (92, .pred p8), (93, .pred p4), (94, .pred p2)] ++
        coordinateArgs tiles heads work batches b) 324
      ((1765, b32 (widthBits p16 p8 p4 p2)) :: coordinateArgs tiles heads work batches b) := by
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
private theorem chooseSectionWidth (l : Launch) (g : Nat) {tiles heads work batches b : Nat}
    (hTiles : 256 * tiles < 2 ^ 31) (hHeads : heads < 2 ^ 31) :
    Seg kernel [] l g 6 320
      ([(91, .pred (decide (800 < 32 * tiles))), (92, .pred (decide (800 < 16 * tiles))),
        (93, .pred (decide (800 < 8 * tiles))), (94, .pred (decide (800 < 4 * tiles)))] ++
        coordinateArgs tiles heads work batches b)
      326 ([(1766, b32 (sectionWidth tiles heads)),
        (1767, b32 (sectionWidth tiles heads * tiles))] ++
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
  have hFinal : Seg kernel [] l g 2 324
      ((1765, b32 cap) :: coordinateArgs tiles heads work batches b)
      326 ([(1766, b32 width), (1767, b32 (width * tiles))] ++
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
private theorem divideHeadSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < 2 ^ 31) (hSpan : width * tiles < 2 ^ 31) (hSpan0 : 0 < width * tiles) :
    Seg kernel [] l g 6 326
      ([(1766, b32 width), (1767, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) 332
      ([(97, .pred false), (1768, b32 (work / (width * tiles))),
        (1766, b32 width), (1767, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let span := width * tiles
  let q := work / span
  let u := next (setReg t 1768 (b32 q))
  have ha : t.regs 1756 = some (b32 work) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs])
  have hb : t.regs 1767 = some (b32 span) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs, span])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_326 ht ha hb hWork hSpan hSpan0
  have hu := ht.set (r := 1768) (v := b32 q) (by simp [coordinateArgs])
  have hXor : span ^^^ work < 2 ^ 31 := Nat.xor_lt_two_pow hSpan hWork
  have hWord := xorWord (a := span) (b := work) hSpan hWork
  have hXor32 : span ^^^ work < 2 ^ 32 := by omega
  have hWork32 : work < 2 ^ 32 := by omega
  have hSpan32 : span < 2 ^ 32 := by omega
  have hz : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hPos : ¬(↑(span ^^^ work) : Int) < 0 := by omega
  have hSteps : ∃ v, run kernel [] l g 5 u = some v ∧
      At v 332 ([(97, .pred false), (1768, b32 q), (1766, b32 width), (1767, b32 span)] ++
        coordinateArgs tiles heads work batches b) := by
    change At u 327
      ((1768, b32 q) :: [(1766, b32 width), (1767, b32 span)] ++
        coordinateArgs tiles heads work batches b) at hu
    simp only [coordinateArgs, List.cons_append, List.nil_append] at hu ⊢
    seg_fp hu using
      simp only [truncBits_ofNat hWork32 (by decide), truncBits_ofNat hSpan32 (by decide),
        hWord, truncBits_ofNat hXor32 (by decide), compare, Option.getD_some,
        signedWord hXor, hz, hPos, decide_false, Bool.and_false]
  obtain ⟨v, hTail, hv⟩ := hSteps
  exact ⟨v, run_comp hRun hTail, hv⟩

/-- Compute a section's relative index and choose whether it needs a shortened final stride. -/
private theorem sectionOffsets (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < tiles * heads) (hItems : tiles * heads < 2 ^ 31)
    (hWidth : width ≤ 16) (hHeads : heads ≤ 2 ^ 25)
    (hSpan : width * tiles < 2 ^ 31) :
    Seg kernel [] l g 8 332
      ([(97, .pred false), (1768, b32 (work / (width * tiles))),
        (1766, b32 width), (1767, b32 (width * tiles))] ++
        coordinateArgs tiles heads work batches b)
      340
      ([(1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work)),
        (1777, b32 (heads - sectionHead tiles width work)), (1766, b32 width),
        (98, .pred (decide (heads < sectionHead tiles width work + width)))] ++
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
  change At t 332
    ([(97, .pred false), (1768, b32 q), (1766, b32 width), (1767, b32 span)] ++
      coordinateArgs tiles heads work batches b) at ht
  change ∃ u, run kernel [] l g 8 t = some u ∧
    At u 340
      ([(1774, b32 (work % span)), (1775, b32 start), (1777, b32 (heads - start)),
        (1766, b32 width), (98, .pred (decide (heads < start + width)))] ++
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

private theorem trimSection (l : Launch) (g : Nat) {tiles heads work batches b width : Nat} :
    Seg kernel [] l g 1 340
      ([(1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work)),
        (1777, b32 (heads - sectionHead tiles width work)), (1766, b32 width),
        (98, .pred (decide (heads < sectionHead tiles width work + width)))] ++
        coordinateArgs tiles heads work batches b) 341
      ([(1778, b32 (sectionStride tiles heads width work)),
        (1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work))] ++
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
    Seg kernel [] l g 6 341
      ([(1778, b32 (sectionStride tiles heads width work)),
        (1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) 347
      ([(101, .pred false),
        (1779, b32 (work % (width * tiles) / sectionStride tiles heads width work)),
        (1778, b32 (sectionStride tiles heads width work)),
        (1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) := by
  intro t ht
  let pos := work % (width * tiles)
  let stride := sectionStride tiles heads width work
  let first := sectionHead tiles width work
  let q := pos / stride
  let u := next (setReg t 1779 (b32 q))
  have ha : t.regs 1774 = some (b32 pos) := holds_mem ht.2.2.2.2 (by simp [coordinateArgs, pos])
  have hb : t.regs 1778 = some (b32 stride) :=
    holds_mem ht.2.2.2.2 (by simp [coordinateArgs, stride])
  have hRun : run kernel [] l g 1 t = some u :=
    runUnsignedRangeDiv Flow.code_341 ht ha hb hPos hStride hStride0
  have hu := ht.set (r := 1779) (v := b32 q) (by simp [coordinateArgs])
  have hXor : stride ^^^ pos < 2 ^ 31 := Nat.xor_lt_two_pow hStride hPos
  have hWord := xorWord (a := stride) (b := pos) hStride hPos
  have hXor32 : stride ^^^ pos < 2 ^ 32 := by omega
  have hPos32 : pos < 2 ^ 32 := by omega
  have hStride32 : stride < 2 ^ 32 := by omega
  have hz : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := rfl
  have hNonneg : ¬(↑(stride ^^^ pos) : Int) < 0 := by omega
  have hSteps : ∃ v, run kernel [] l g 5 u = some v ∧
      At v 347
        ([(101, .pred false), (1779, b32 q), (1778, b32 stride), (1774, b32 pos),
          (1775, b32 first)] ++ coordinateArgs tiles heads work batches b) := by
    change At u 342
      ((1779, b32 q) :: [(1778, b32 stride), (1774, b32 pos), (1775, b32 first)] ++
        coordinateArgs tiles heads work batches b) at hu
    simp only [coordinateArgs, List.cons_append, List.nil_append] at hu ⊢
    seg_fp hu using
      simp only [truncBits_ofNat hPos32 (by decide), truncBits_ofNat hStride32 (by decide),
        hWord, truncBits_ofNat hXor32 (by decide), compare, Option.getD_some,
        signedWord hXor, hz, hNonneg, decide_false, Bool.and_false]
  obtain ⟨v, hTail, hv⟩ := hSteps
  exact ⟨v, run_comp hRun hTail, hv⟩

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

private theorem reversedTileWord {tiles back : Nat} (ht : tiles < 2 ^ 32) (hb : back < tiles) :
    truncBits 32 (BitVec.ofNat 64 tiles + truncBits 32 (~~~BitVec.ofNat 64 back)) =
      BitVec.ofNat 64 (tiles - 1 - back) := by
  have hNot : truncBits 32 (~~~BitVec.ofNat 64 back) =
      BitVec.ofNat 64 (4294967295 - back) := by
    apply BitVec.eq_of_toNat_eq
    rw [truncBits, BitVec.toNat_not, toNat_ofNat_lt (show back < 2 ^ 64 by omega),
      toNat_ofNat_lt (show _ < 2 ^ 64 from lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
      toNat_ofNat_lt (show 4294967295 - back < 2 ^ 64 by omega)]
    omega
  rw [hNot, ← BitVec.ofNat_add]
  have hNormalize : tiles + (4294967295 - back) =
      2 ^ 32 + (tiles - 1 - back) := by omega
  rw [hNormalize, truncBits, toNat_ofNat_lt (show 2 ^ 32 + (tiles - 1 - back) < 2 ^ 64 by omega),
    Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (show tiles - 1 - back < 2 ^ 32 by omega)]

/-- Recover the head from the section remainder and walk tiles in reverse order. -/
private theorem writeTileCoordinates (l : Launch) (g : Nat) {tiles heads work batches b width : Nat}
    (hWork : work < tiles * heads) (hItems : tiles * heads < 2 ^ 31) (hWidth : 0 < width)
    (hTiles : tiles < 2 ^ 32) (hHeads : heads < 2 ^ 31)
    (hStride : sectionStride tiles heads width work < 2 ^ 31) :
    let pos := sectionCoords tiles heads width work
    Seg kernel [] l g 7 347
      ([(101, .pred false),
        (1779, b32 (work % (width * tiles) / sectionStride tiles heads width work)),
        (1778, b32 (sectionStride tiles heads width work)),
        (1774, b32 (work % (width * tiles))), (1775, b32 (sectionHead tiles width work))] ++
        coordinateArgs tiles heads work batches b) 354
      [(7170, b32 b), (7144, b32 batches), (7169, b32 pos.2), (7168, b32 pos.1)] := by
  dsimp only
  intro t ht
  let pos := work % (width * tiles)
  let stride := sectionStride tiles heads width work
  let start := sectionHead tiles width work
  let back := pos / stride
  have ht0 : 0 < tiles := Nat.pos_of_ne_zero fun h => by simp [h] at hWork
  have hs0 : 0 < stride := by
    apply Nat.lt_min.mpr
    exact ⟨hWidth, by have := sectionHead_lt (width := width) hWork; omega⟩
  have hPos : pos < stride * tiles := sectionPos_lt hWork hWidth
  have hBack : back < tiles := (Nat.div_lt_iff_lt_mul hs0).2 (by simpa [Nat.mul_comm] using hPos)
  have hS : start < heads := sectionHead_lt hWork
  have hPos32 : pos < 2 ^ 32 := by have := Nat.mod_le work (width * tiles); omega
  have hs32 : stride < 2 ^ 32 := by omega
  have hStart32 : start < 2 ^ 32 := by omega
  have hBack32 : back < 2 ^ 32 := by omega
  have hProd : back * stride ≤ pos := Nat.div_mul_le_self pos stride
  have hProd32 : back * stride < 2 ^ 32 := by omega
  have hPosStart32 : pos + start < 2 ^ 32 := by
    have hJoin : pos + start * tiles = work := by
      simpa only [pos, start, sectionHead, Nat.mul_assoc] using
        Nat.mod_add_div' work (width * tiles)
    have h := Nat.le_mul_of_pos_right start ht0
    omega
  have hFinalHead : pos + start - back * stride = start + pos % stride := by
    have h := Nat.mod_add_div' pos stride
    change pos % stride + back * stride = pos at h
    omega
  have hHead32 : start + pos % stride < 2 ^ 32 := by
    have := Nat.mod_le pos stride
    omega
  change At t 347
    ([(101, .pred false), (1779, b32 back), (1778, b32 stride),
      (1774, b32 pos), (1775, b32 start)] ++ coordinateArgs tiles heads work batches b) at ht
  change ∃ u, run kernel [] l g 7 t = some u ∧
    At u 354
      [(7170, b32 b), (7144, b32 batches), (7169, b32 (start + pos % stride)),
        (7168, b32 (tiles - 1 - back))]
  simp only [coordinateArgs, List.cons_append, List.nil_append] at ht
  have hz : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have hz32 : truncBits 32 0 = 0 := rfl
  have hZero : BitVec.ofNat 64 back + 0 = BitVec.ofNat 64 back := BitVec.add_zero _
  seg_fp ht using
    simp only [b32, hz, hz32, hZero, truncBits_ofNat hBack32 (by decide),
      truncBits_ofNat hs32 (by decide),
      truncBits_ofNat hPos32 (by decide), truncBits_ofNat hStart32 (by decide),
      truncBits_ofNat hTiles (by decide), truncBits_idem, reversedTileWord hTiles hBack,
      ← BitVec.ofNat_mul, ← BitVec.ofNat_add, truncBits_ofNat hProd32 (by decide),
      truncBits_ofNat hPosStart32 (by decide),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show back * stride < 2 ^ 64 by omega)
        (show back * stride ≤ pos + start by omega),
      hFinalHead, truncBits_ofNat hHead32 (by decide)]


/-- The loader's section mapper obtains the same reversed tile and head coordinates as
the epilogue, using its own decoded integer instructions and physical registers. -/
theorem loaderTileHead {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch item : Nat} (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ item)
    (hHi : item < tilePrefix p (batch + 1) * p.heads) :
    let pos := assignedCoordinates p batch item
    Seg kernel [] l g 43 311
      [(1754, b32 (requestTiles p batch)), (7136, b32 p.heads),
       (1756, b32 (item - tilePrefix p batch * p.heads)), (7154, b32 800),
       (7144, b32 p.batch), (7170, b32 batch)] 354
      [(7170, b32 batch), (7144, b32 p.batch), (7169, b32 pos.2), (7168, b32 pos.1)] := by
  dsimp only
  let tiles := requestTiles p batch
  let width := sectionWidth tiles p.heads
  let work := item - tilePrefix p batch * p.heads
  have hEnd : item < tilePrefix p batch * p.heads + tiles * p.heads := by
    simpa only [tilePrefix_succ, Nat.add_mul, tiles] using hHi
  have hWork : work < tiles * p.heads := by
    dsimp [work]
    omega
  have hPrefixBounds := hp.prefixWork_signed (show batch + 1 ≤ p.batch by omega)
  have hItems : tiles * p.heads < 2 ^ 31 := by
    rw [tilePrefix_succ, Nat.add_mul] at hPrefixBounds
    exact lt_of_le_of_lt (Nat.le_add_left _ _) hPrefixBounds
  have hWork31 := hWork.trans hItems
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
  have hTile32 : tiles < 2 ^ 32 := by omega
  have hHeadsFit : p.heads ≤ 2 ^ 25 := by
    have hO := hp.ranges p.oRegion (by simp)
    change p.oBase + 512 * p.heads * p.totalQ ≤ 2 ^ 64 at hO
    have hr := hp.raggedBase
    rw [← Nat.mul_assoc] at hr
    omega
  exact (widthThresholds l g hTiles).comp
    ((chooseSectionWidth l g hTiles hHeads).comp
    ((divideHeadSection l g hWork31 hSpan hSpanPos).comp
    ((sectionOffsets l g hWork hItems hWidth16 hHeadsFit hSpan).comp
    ((trimSection l g).comp
    ((divideSectionTile l g hRelative hStride hStridePos).comp
      (writeTileCoordinates l g hWork hItems hWidth hTile32 hHeads hStride))))))

end
end PTX.Kernels.TmlFa4Fwd.Loader
