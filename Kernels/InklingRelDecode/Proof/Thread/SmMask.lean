-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmPackBase

@[expose] public section

/-! # The mask of the next block's bias loads (pcs 1051-1056)

`%p92 = row_valid && (i + 1 < num_iters) && (block + num_splits >= n_bias)`. The iteration count
is compared as a signed 64-bit number against the sign extension of the 32-bit block count
(`setp.lt.s64`, pc 1054); a block count of `2 ^ 31` or more is negative there, so the
comparison is false. A segment that evaluates that comparison inside a `theorem` exceeds the
kernel's recursion depth, so the comparison is proved once, as `cmp_lt_s64`, and each piece is one
instruction (or the last two). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

theorem sxw_small {b : Nat} (hb : b < 2 ^ 31) : sxw b = b := by
  have h1 : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
  have h2 : b / 2 ^ 31 = 0 := by omega
  unfold sxw
  rw [h1, h2]
  simp

theorem sxw_big {b : Nat} (hb : 2 ^ 31 ≤ b) (hb' : b < 2 ^ 32) : sxw b = b + (2 ^ 64 - 2 ^ 32) := by
  have h1 : b % 2 ^ 32 = b := Nat.mod_eq_of_lt hb'
  have h2 : b / 2 ^ 31 = 1 := by omega
  unfold sxw
  rw [h1, h2]
  simp

theorem cmp_lt_s64_neg (a c : Nat) (ha : a < 2 ^ 63) (hc1 : 2 ^ 63 ≤ c) (hc2 : c < 2 ^ 64) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 c)) = false := by
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc2
  simp only [PTX.compare, toSigned64_ofNat, h1, h2]
  have e1 : a < 2 ^ 63 := ha
  have e2 : ¬ c < 2 ^ 63 := by omega
  simp only [e1, e2, ↓reduceIte, decide_eq_false_iff_not]
  omega

theorem cmp_lt_s64_pos (a c : Nat) (ha : a < 2 ^ 63) (hc : c < 2 ^ 63) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 c)) = decide (a < c) := by
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  simp only [PTX.compare, toSigned64_ofNat, h1, h2, ha, hc, ↓reduceIte, decide_eq_decide]
  omega

/-- Signed 32-bit `>=` of two words below `2 ^ 31`. -/
theorem cmp_ge_s32 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    PTX.compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = decide (b ≤ a) := by
  simp only [PTX.compare, toSigned32_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), ha, hb, ↓reduceIte, ge_iff_le, decide_eq_decide]
  omega

/-- Signed 64-bit `<` of a counter below `2 ^ 63` and the sign extension of a word. -/
theorem cmp_lt_s64 (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 32) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 (sxw b))) = decide (a < b ∧ b < 2 ^ 31) := by
  by_cases hb31 : b < 2 ^ 31
  · rw [sxw_small hb31, cmp_lt_s64_pos a b ha (by omega), decide_eq_decide]
    omega
  · have h : 2 ^ 63 ≤ sxw b := by rw [sxw_big (by omega) hb]; omega
    have h' : sxw b < 2 ^ 64 := by rw [sxw_big (by omega) hb]; omega
    rw [cmp_lt_s64_neg a _ ha h h', Bool.false_eq, decide_eq_false_iff_not]
    omega

theorem seg_1051 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) :
    Seg kernel asms L g 1 1051 (factsAt L g 1051 d) 1052 (factsAt L g 1052 d) := by
  have := hok.splits
  intro t h
  sm_seg h [blkOf]

theorem seg_1052 (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i ≤ d.e.r26) :
    Seg kernel asms L g 1 1052 (factsAt L g 1052 d) 1053 (factsAt L g 1053 d) := by
  have := hok.nbias
  have : d.n + d.e.splits < 2 ^ 31 := hok.blk_lt hi
  have e : (d.n + d.e.splits) % 2 ^ 32 = d.n + d.e.splits := Nat.mod_eq_of_lt (by omega)
  intro t h
  seg_fp h using
    sm_vals
    all_goals (simp only [Value.pred.injEq, e]; rw [cmp_ge_s32 _ _ (by omega) (by omega)])

theorem seg_1053 (d : D) (hT : g % L.block < 128) (hi : d.i ≤ d.e.r26) (hok : d.e.Ok) :
    Seg kernel asms L g 1 1053 (factsAt L g 1053 d) 1054 (factsAt L g 1054 d) := by
  have := hok.r26_lt
  intro t h
  sm_seg h

theorem seg_1054 (d : D) (hT : g % L.block < 128) (hi : d.i ≤ d.e.r26) (hok : d.e.Ok) :
    Seg kernel asms L g 1 1054 (factsAt L g 1054 d) 1055 (factsAt L g 1055 d) := by
  have := hok.r26_lt
  have := hok.r25
  intro t h
  seg_fp h using
    sm_vals
    all_goals (simp only [Value.pred.injEq]; rw [cmp_lt_s64 _ _ (by omega) (by omega)])

theorem seg_1055 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 2 1055 (factsAt L g 1055 d) 1057 (factsAt L g 1057 d) := by
  intro t h
  seg_fp h using
    sm_vals
    all_goals (simp only [Value.pred.injEq, actB, Bool.and_assoc, D.n, blkOf]; try rfl)

/-- **The mask of the next block's loads** (pcs 1051 to 1056): `%p92` is `actB`. -/
theorem seg_mask (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i ≤ d.e.r26) :
    Seg kernel asms L g 6 1051 (factsAt L g 1051 d) 1057 (factsAt L g 1057 d) := by
  have h1 := (seg_1051 d hT hok).comp (seg_1052 d hT hok hi)
  have h2 := h1.comp (seg_1053 d hT hi hok)
  have h3 := h2.comp (seg_1054 d hT hi hok)
  have h4 := h3.comp (seg_1055 d hT)
  exact Seg.of_len h4 rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
