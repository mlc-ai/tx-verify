-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmScZ

@[expose] public section

/-! # The visibility predicates (pcs 1564-1627)

The 64 comparisons `setp.gt.s32 %p, %r, -1` of the difference registers (and `setp.lt.s32 %p161,
%r678, 0` for the second column) between the facts of the mask's table: each predicate is the
column's visibility. The signed comparisons are decided once, as `cmp_gt_m1` and `cmp_lt_0`, because
a segment that evaluates them exceeds the kernel's recursion depth. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

theorem toSigned_m1 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := by decide +kernel
theorem toSigned_0 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 := by decide +kernel

theorem compare_gt_s (a b : BitVec 64) :
    compare Cmp.gt IType.s 32 a b = decide (toSigned 32 b < toSigned 32 a) := by
  simp only [PTX.compare, gt_iff_lt]

theorem compare_lt_s (a b : BitVec 64) :
    compare Cmp.lt IType.s 32 a b = decide (toSigned 32 a < toSigned 32 b) := by
  simp only [PTX.compare]

theorem cmp_gt_m1 (P Q : Nat) (hP : P < 2 ^ 31) (hQ : Q < 2 ^ 31) :
    compare Cmp.gt IType.s 32 (truncBits 32 (BitVec.ofNat 64 ((P + 2 ^ 32 - Q) % 2 ^ 32)))
      (truncBits 32 (BitVec.ofInt 64 (-1))) = decide (Q ≤ P) := by
  rw [compare_gt_s, toSigned_m1, toSigned32_ofNat, Nat.mod_mod]
  by_cases h : Q ≤ P
  · have e : (P + 2 ^ 32 - Q) % 2 ^ 32 = P - Q := by omega
    rw [e]
    have h2 : P - Q < 2 ^ 31 := by omega
    rw [if_pos h2, decide_eq_decide]
    omega
  · have e : (P + 2 ^ 32 - Q) % 2 ^ 32 = P + 2 ^ 32 - Q := by omega
    rw [e]
    have h2 : ¬ (P + 2 ^ 32 - Q < 2 ^ 31) := by omega
    rw [if_neg h2, decide_eq_decide]
    omega

theorem cmp_lt_0 (P Q : Nat) (hP : P < 2 ^ 31) (hQ : Q < 2 ^ 31) :
    compare Cmp.lt IType.s 32 (truncBits 32 (BitVec.ofNat 64 ((Q + 2 ^ 32 - P) % 2 ^ 32)))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (Q < P) := by
  rw [compare_lt_s, toSigned_0, toSigned32_ofNat, Nat.mod_mod]
  by_cases h : Q < P
  · have e : (Q + 2 ^ 32 - P) % 2 ^ 32 = Q + 2 ^ 32 - P := by omega
    rw [e]
    have h2 : ¬ (Q + 2 ^ 32 - P < 2 ^ 31) := by omega
    rw [if_neg h2, decide_eq_decide]
    omega
  · have e : (Q + 2 ^ 32 - P) % 2 ^ 32 = Q - P := by omega
    rw [e]
    have h2 : Q - P < 2 ^ 31 := by omega
    rw [if_pos h2, decide_eq_decide]
    omega

set_option hygiene false in
/-- `%p = (diff > -1)` of a difference register: the column's visibility. -/
macro "sz_gt" : tactic =>
  `(tactic| (simp only [Value.pred.injEq, scored_n, scored_e, visK, diffN, colOfP, Nat.reduceMod,
               Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, Nat.reduceEqDiff]
             rw [cmp_gt_m1 _ _ (by omega) (by omega)]
             try rfl))

theorem tok_lt (T : Nat) : tokOf T < 64 := by
  simp only [tokOf, row]
  omega

theorem half_lt (T : Nat) : half T < 2 := by
  simp only [half]
  omega

theorem pred_1564 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1564 (factsZ L g 1564 d) 1572
      (factsZ L g 1572 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1572 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1572 (factsZ L g 1572 d) 1580
      (factsZ L g 1580 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1580 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1580 (factsZ L g 1580 d) 1588
      (factsZ L g 1588 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1588 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1588 (factsZ L g 1588 d) 1596
      (factsZ L g 1596 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1596 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1596 (factsZ L g 1596 d) 1604
      (factsZ L g 1604 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1604 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1604 (factsZ L g 1604 d) 1612
      (factsZ L g 1612 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1612 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 8 1612 (factsZ L g 1612 d) 1620
      (factsZ L g 1620 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1620 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 7 1620 (factsZ L g 1620 d) 1627
      (factsZ L g 1627 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals sz_gt

theorem pred_1627 (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 1 1627 (factsZ L g 1627 d) 1628
      (factsZ L g 1628 d) := by
  have := hR.blk
  have := hR.past
  have := tok_lt (g % L.block)
  have := half_lt (g % L.block)
  intro t h
  seg_fp h using
    sz_vals
    all_goals (simp only [Value.pred.injEq, visK, diff1]
               rw [cmp_lt_0 _ _ (by omega) (by omega)]
               congr 1
               exact propext (by omega))

/-- **The visibility predicates** (pcs 1564 to 1627). -/
theorem seg_preds (d : D) (hT : g % L.block < 128) (hR : Rng d.e (g % L.block) d.n) :
    Seg kernel asms L g 64 1564 (factsZ L g 1564 d) 1628
      (factsZ L g 1628 d) := by
  have h0 := pred_1564 d hT hR
  have h1 := h0.comp (pred_1572 d hT hR)
  have h2 := h1.comp (pred_1580 d hT hR)
  have h3 := h2.comp (pred_1588 d hT hR)
  have h4 := h3.comp (pred_1596 d hT hR)
  have h5 := h4.comp (pred_1604 d hT hR)
  have h6 := h5.comp (pred_1612 d hT hR)
  have h7 := h6.comp (pred_1620 d hT hR)
  exact Seg.of_len (h7.comp (pred_1627 d hT hR)) rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
