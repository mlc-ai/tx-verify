-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumOps

@[expose] public section

/-! # The valid-mask chain against the mask word

`w0m_col i`: on a mask word `n` (a 32-bit word, "reads as"), the register the chain writes for
column `i` (`Gen.mask_v304`, ...) holds the high-half score word of the column if bit `i` of `n`
is set and the pattern of negative infinity otherwise. The registers of the chain's source
values first: the shifted words, the halfwords and the sign bytes of `n`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

section Vals

variable (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
  (h : V 1002 = .bits 32 (BitVec.ofNat 64 n))
include hn h

theorem w0m_v292 : mask_v292 V = .bits 32 (BitVec.ofNat 64 (n / 2 ^ 8)) := by
  rw [mask_v292, mask_op292, h, w0m_shr (k := 8) (kn := 8) rfl hn (by norm_num)]; rfl

theorem w0m_v296 : mask_v296 V = .bits 32 (BitVec.ofNat 64 (n / 2 ^ 16)) := by
  rw [mask_v296, mask_op296, h, w0m_shr (k := 16) (kn := 16) rfl hn (by norm_num)]; rfl

theorem w0m_v300 : mask_v300 V = .bits 32 (BitVec.ofNat 64 (n / 2 ^ 24)) := by
  rw [mask_v300, mask_op300, h, w0m_shr (k := 24) (kn := 24) rfl hn (by norm_num)]; rfl

omit hn in
theorem w0m_v291 : mask_v291 V = .bits 16 (BitVec.ofNat 64 (n / 2 ^ 0 % 65536)) := by
  rw [mask_v291, show mask_op291 = w0mCvtU16 156 1002 from rfl, h, w0m_cvt_u16]
  simp [w0m_okVal]

theorem w0m_v295 : mask_v295 V = .bits 16 (BitVec.ofNat 64 (n / 2 ^ 8 % 65536)) := by
  rw [mask_v295, show mask_op295 = w0mCvtU16 158 1003 from rfl, w0m_v292 V n hn h,
    w0m_cvt_u16]
  rfl

theorem w0m_v301 : mask_v301 V = .bits 16 (BitVec.ofNat 64 (n / 2 ^ 24 % 65536)) := by
  rw [mask_v301, show mask_op301 = w0mCvtU16 161 1007 from rfl, w0m_v300 V n hn h,
    w0m_cvt_u16]
  rfl

theorem w0m_v299 : mask_v299 V = .bits 16 (BitVec.ofNat 64 (n / 2 ^ 16 % 65536)) := by
  simp [mask_v299, sinkW, okVal, lk, h, splitValue, Value.bytes, pure, Except.pure]
  rw [Nat.mod_eq_of_lt (by omega : n < 18446744073709551616)]
  apply BitVec.eq_of_toNat_eq
  simp [truncBits]

omit hn in
theorem w0m_v290 : mask_v290 V = .bits 16 (BitVec.ofNat 64 (w0mSx (n / 2 ^ 0 % 256))) := by
  rw [mask_v290, show mask_op290 = w0mCvtS8 155 1002 from rfl, h, w0m_cvt_s8]
  simp [w0m_okVal]

theorem w0m_v293 : mask_v293 V = .bits 32 (BitVec.ofNat 64 (if n / 2 ^ 8 % 256 < 128
    then n / 2 ^ 8 % 256 else n / 2 ^ 8 % 256 + 4294967040)) := by
  rw [mask_v293]
  show okVal _ (bfeW .s 32 (.reg 1002) (.imm ((8 : Nat) : Int)) (.imm 8)
    (lk [1002] [V 1002])) = _
  rw [h, w0m_bfe hn (by norm_num)]; rfl

theorem w0m_v297 : mask_v297 V = .bits 32 (BitVec.ofNat 64 (if n / 2 ^ 16 % 256 < 128
    then n / 2 ^ 16 % 256 else n / 2 ^ 16 % 256 + 4294967040)) := by
  rw [mask_v297]
  show okVal _ (bfeW .s 32 (.reg 1002) (.imm ((16 : Nat) : Int)) (.imm 8)
    (lk [1002] [V 1002])) = _
  rw [h, w0m_bfe hn (by norm_num)]; rfl

theorem w0m_v294 : mask_v294 V = .bits 16 (BitVec.ofNat 64 (w0mSx (n / 2 ^ 8 % 256))) := by
  rw [mask_v294, show mask_op294 = w0mCvtS8 157 1004 from rfl, w0m_v293 V n hn h, w0m_cvt_s8]
  simp only [w0m_okVal]
  congr 3
  split_ifs <;> omega

theorem w0m_v298 : mask_v298 V = .bits 16 (BitVec.ofNat 64 (w0mSx (n / 2 ^ 16 % 256))) := by
  rw [mask_v298, show mask_op298 = w0mCvtS8 159 1006 from rfl, w0m_v297 V n hn h, w0m_cvt_s8]
  simp only [w0m_okVal]
  congr 3
  split_ifs <;> omega

end Vals


theorem w0m_col0 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2918).bytes = 4) :
    mask_v304 V = if n.testBit 0 = true then V 2918 else w0NegInf :=
  w0m_colA hn (by simpa using h) (by decide) hv

theorem w0m_col1 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2919).bytes = 4) :
    mask_v307 V = if n.testBit 1 = true then V 2919 else w0NegInf :=
  w0m_colB (b := 1) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col2 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2920).bytes = 4) :
    mask_v310 V = if n.testBit 2 = true then V 2920 else w0NegInf :=
  w0m_colB (b := 2) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col3 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2921).bytes = 4) :
    mask_v313 V = if n.testBit 3 = true then V 2921 else w0NegInf :=
  w0m_colB (b := 3) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col4 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2922).bytes = 4) :
    mask_v316 V = if n.testBit 4 = true then V 2922 else w0NegInf :=
  w0m_colB (b := 4) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col5 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2923).bytes = 4) :
    mask_v319 V = if n.testBit 5 = true then V 2923 else w0NegInf :=
  w0m_colB (b := 5) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col6 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2924).bytes = 4) :
    mask_v322 V = if n.testBit 6 = true then V 2924 else w0NegInf :=
  w0m_colB (b := 6) (by norm_num) (by norm_num) (w0m_v291 V n h) (by decide) hv

theorem w0m_col7 (V : Nat → Value) (n : Nat) (_hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2925).bytes = 4) :
    mask_v324 V = if n.testBit 7 = true then V 2925 else w0NegInf :=
  w0m_colC (w0m_v290 V n h) (by decide) hv

theorem w0m_col8 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2926).bytes = 4) :
    mask_v327 V = if n.testBit 8 = true then V 2926 else w0NegInf :=
  w0m_colA hn (w0m_v292 V n hn h) (by decide) hv

theorem w0m_col9 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2927).bytes = 4) :
    mask_v330 V = if n.testBit 9 = true then V 2927 else w0NegInf :=
  w0m_colB (b := 1) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col10 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2928).bytes = 4) :
    mask_v333 V = if n.testBit 10 = true then V 2928 else w0NegInf :=
  w0m_colB (b := 2) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col11 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2929).bytes = 4) :
    mask_v336 V = if n.testBit 11 = true then V 2929 else w0NegInf :=
  w0m_colB (b := 3) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col12 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2930).bytes = 4) :
    mask_v339 V = if n.testBit 12 = true then V 2930 else w0NegInf :=
  w0m_colB (b := 4) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col13 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2931).bytes = 4) :
    mask_v342 V = if n.testBit 13 = true then V 2931 else w0NegInf :=
  w0m_colB (b := 5) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col14 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2932).bytes = 4) :
    mask_v345 V = if n.testBit 14 = true then V 2932 else w0NegInf :=
  w0m_colB (b := 6) (by norm_num) (by norm_num) (w0m_v295 V n hn h) (by decide) hv

theorem w0m_col15 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2933).bytes = 4) :
    mask_v347 V = if n.testBit 15 = true then V 2933 else w0NegInf :=
  w0m_colC (w0m_v294 V n hn h) (by decide) hv

theorem w0m_col16 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2934).bytes = 4) :
    mask_v350 V = if n.testBit 16 = true then V 2934 else w0NegInf :=
  w0m_colA hn (w0m_v296 V n hn h) (by decide) hv

theorem w0m_col17 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2935).bytes = 4) :
    mask_v353 V = if n.testBit 17 = true then V 2935 else w0NegInf :=
  w0m_colB (b := 1) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col18 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2936).bytes = 4) :
    mask_v356 V = if n.testBit 18 = true then V 2936 else w0NegInf :=
  w0m_colB (b := 2) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col19 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2937).bytes = 4) :
    mask_v359 V = if n.testBit 19 = true then V 2937 else w0NegInf :=
  w0m_colB (b := 3) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col20 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2938).bytes = 4) :
    mask_v362 V = if n.testBit 20 = true then V 2938 else w0NegInf :=
  w0m_colB (b := 4) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col21 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2939).bytes = 4) :
    mask_v365 V = if n.testBit 21 = true then V 2939 else w0NegInf :=
  w0m_colB (b := 5) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col22 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2940).bytes = 4) :
    mask_v368 V = if n.testBit 22 = true then V 2940 else w0NegInf :=
  w0m_colB (b := 6) (by norm_num) (by norm_num) (w0m_v299 V n hn h) (by decide) hv

theorem w0m_col23 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2941).bytes = 4) :
    mask_v370 V = if n.testBit 23 = true then V 2941 else w0NegInf :=
  w0m_colC (w0m_v298 V n hn h) (by decide) hv

theorem w0m_col24 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2942).bytes = 4) :
    mask_v373 V = if n.testBit 24 = true then V 2942 else w0NegInf :=
  w0m_colA hn (w0m_v300 V n hn h) (by decide) hv

theorem w0m_col25 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2943).bytes = 4) :
    mask_v376 V = if n.testBit 25 = true then V 2943 else w0NegInf :=
  w0m_colB (b := 1) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col26 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2944).bytes = 4) :
    mask_v379 V = if n.testBit 26 = true then V 2944 else w0NegInf :=
  w0m_colB (b := 2) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col27 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2945).bytes = 4) :
    mask_v382 V = if n.testBit 27 = true then V 2945 else w0NegInf :=
  w0m_colB (b := 3) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col28 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2946).bytes = 4) :
    mask_v385 V = if n.testBit 28 = true then V 2946 else w0NegInf :=
  w0m_colB (b := 4) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col29 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2947).bytes = 4) :
    mask_v388 V = if n.testBit 29 = true then V 2947 else w0NegInf :=
  w0m_colB (b := 5) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col30 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2948).bytes = 4) :
    mask_v391 V = if n.testBit 30 = true then V 2948 else w0NegInf :=
  w0m_colB (b := 6) (by norm_num) (by norm_num) (w0m_v301 V n hn h) (by decide) hv

theorem w0m_col31 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : (V 2949).bytes = 4) :
    mask_v393 V = if n.testBit 31 = true then V 2949 else w0NegInf :=
  w0m_colD hn h (by decide) hv

/-- The register of column `i` in the mask chain's facts. -/
def w0mReg (i : Nat) : Nat := 1009 + i + i / 8

/-- **The mask chain's facts** (`Gen.mask_facts4`): column `i`'s register holds the high-half word
if bit `i` of the mask word is set, else negative infinity. -/
theorem w0m_facts4 (V : Nat → Value) (n : Nat) (hn : n < 2 ^ 32)
    (h : V 1002 = .bits 32 (BitVec.ofNat 64 n)) (hv : ∀ i < 32, (V (2918 + i)).bytes = 4)
    (i : Nat) (hi : i < 32) :
    lookupD (mask_facts4 V) (w0mReg i) =
      if n.testBit i = true then V (2918 + i) else w0NegInf := by
  match i, hi with
  | 0, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col0 V n hn h (hv 0 (by norm_num))
  | 1, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col1 V n hn h (hv 1 (by norm_num))
  | 2, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col2 V n hn h (hv 2 (by norm_num))
  | 3, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col3 V n hn h (hv 3 (by norm_num))
  | 4, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col4 V n hn h (hv 4 (by norm_num))
  | 5, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col5 V n hn h (hv 5 (by norm_num))
  | 6, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col6 V n hn h (hv 6 (by norm_num))
  | 7, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col7 V n hn h (hv 7 (by norm_num))
  | 8, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col8 V n hn h (hv 8 (by norm_num))
  | 9, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col9 V n hn h (hv 9 (by norm_num))
  | 10, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col10 V n hn h (hv 10 (by norm_num))
  | 11, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col11 V n hn h (hv 11 (by norm_num))
  | 12, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col12 V n hn h (hv 12 (by norm_num))
  | 13, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col13 V n hn h (hv 13 (by norm_num))
  | 14, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col14 V n hn h (hv 14 (by norm_num))
  | 15, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col15 V n hn h (hv 15 (by norm_num))
  | 16, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col16 V n hn h (hv 16 (by norm_num))
  | 17, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col17 V n hn h (hv 17 (by norm_num))
  | 18, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col18 V n hn h (hv 18 (by norm_num))
  | 19, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col19 V n hn h (hv 19 (by norm_num))
  | 20, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col20 V n hn h (hv 20 (by norm_num))
  | 21, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col21 V n hn h (hv 21 (by norm_num))
  | 22, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col22 V n hn h (hv 22 (by norm_num))
  | 23, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col23 V n hn h (hv 23 (by norm_num))
  | 24, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col24 V n hn h (hv 24 (by norm_num))
  | 25, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col25 V n hn h (hv 25 (by norm_num))
  | 26, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col26 V n hn h (hv 26 (by norm_num))
  | 27, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col27 V n hn h (hv 27 (by norm_num))
  | 28, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col28 V n hn h (hv 28 (by norm_num))
  | 29, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col29 V n hn h (hv 29 (by norm_num))
  | 30, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col30 V n hn h (hv 30 (by norm_num))
  | 31, _ =>
    simpa [mask_facts4, lookupD, w0mReg, List.lookup] using
      w0m_col31 V n hn h (hv 31 (by norm_num))
  | _ + 32, hi => exact absurd hi (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
