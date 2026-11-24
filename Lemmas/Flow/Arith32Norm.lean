-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Word

@[expose] public section

/-! # Word arithmetic by rewriting, with the bounds from the context

A proof tool. A value table that mirrors the code (`Tools/machine_gen.py`, rule M2) holds the
code's terms in the 32-bit vocabulary (`Lemmas/Flow/Arith32.lean`); a role's reference invariant
states their closed forms over natural numbers. On small words (`W n`) every operation of the
vocabulary is the operation on numbers (`Lemmas/Flow/Arith32Word.lean`) under bounds that are
linear facts about the numbers. `w32_norm [lemmas] at loc` rewrites with all of them at once and
discharges each bound by `omega` from the hypotheses in context, so a closed-form proof states its
bounds once (as `have`s) instead of passing a `(by omega)` to each rewrite:

```
have hw := work_lt hp hb      -- the bounds, once
w32_norm [A, hT, H_W hp]      -- every `add32`, `mad32`, comparison ... of small words
```

The role's own word lemmas (its launch words, its table's entries) are the extra `lemmas`; the
comparisons of a word with an immediate (`scmpi`) are here for the `.b`, `.u` and `.s` kinds. -/

namespace PTX.Flow.Arith32
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem i32_toNat_int {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 31) : (i32 n).toNat = n.toNat := by
  simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega

/-- An immediate below `2 ^ 31` is the word of its number. -/
theorem i32_int {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 31) : i32 n = W n.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [i32_toNat_int h0 hn, toNat_W (by omega)]

theorem addi_int {a : Nat} {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 31) (h : a + n.toNat < 2 ^ 32) :
    addi (W a) n = W (a + n.toNat) := by
  have := addi_W (a := a) (n := n.toNat) (by omega) h
  rwa [show ((n.toNat : Nat) : Int) = n by omega] at this

theorem shrs_int {a : Nat} {n : Int} (ha : a < 2 ^ 31) (h0 : 0 ≤ n) (hn : n < 32) :
    shrs (W a) n = W (a / 2 ^ n.toNat) := by
  have := toNat_shrs_W ha (k := n.toNat) (by omega)
  rwa [show ((n.toNat : Nat) : Int) = n by omega] at this

theorem shru_int {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 32) :
    shru (W a) n = W (a / 2 ^ n.toNat) := by
  have hi : (i32 n).toNat = n.toNat := i32_toNat_int h0 (by omega)
  simp only [shru, hi, show ¬ n.toNat ≥ 32 by omega, ↓reduceIte, r32_W ha]
  apply BitVec.eq_of_toNat_eq
  have hlt : a / 2 ^ n.toNat < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    toNat_W (show a < 2 ^ 64 by omega), toNat_W hlt]

theorem scmpi_eq_b_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .eq .b (W a) n = decide (a = n.toNat) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem scmpi_ne_b_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .ne .b (W a) n = decide (a ≠ n.toNat) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem scmpi_lt_u_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .lt .u (W a) n = decide (a < n.toNat) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem scmpi_le_u_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .le .u (W a) n = decide (a ≤ n.toNat) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem scmpi_gt_u_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .gt .u (W a) n = decide (n.toNat < a) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem scmpi_ge_u_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi .ge .u (W a) n = decide (n.toNat ≤ a) := by
  simp only [scmpi, PTX.compare, r32_W ha, i32_toNat_int h0 hn, toNat_W (show a < 2 ^ 64 by omega)]
  rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

/-- A signed comparison with a nonnegative immediate is the comparison with its word. -/
theorem scmpi_s_W (c : Cmp) {a : Nat} {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    scmpi c .s (W a) n = scmp c .s (W a) (W n.toNat) := by
  simp only [scmpi, scmp, i32_int h0 hn, r32_W (show n.toNat < 2 ^ 32 by omega)]

theorem scmp_eq_b_W {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    scmp .eq .b (W a) (W b) = decide (a = b) := by
  simp only [scmp, r32_W ha, r32_W hb, PTX.compare, W, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  simp

/-- `w32_norm [lemmas] at loc`: rewrite the code's 32-bit operations on small words to the words
of their numbers (additions, subtractions, products, `mad`, the minimum, shifts, comparisons with
words and immediates), with the extra `lemmas`, discharging every bound by `omega` from the
context. -/
syntax "w32_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic

macro_rules
  | `(tactic| w32_norm $[$loc]?) => `(tactic| w32_norm [] $[$loc]?)
  | `(tactic| w32_norm [$ls,*] $[$loc]?) => `(tactic|
      simp (disch := omega) only [PTX.Flow.Arith32.add32_W, PTX.Flow.Arith32.addi_W,
        PTX.Flow.Arith32.addi_int, PTX.Flow.Arith32.sub32_W,
        PTX.Flow.Arith32.mul32_W, PTX.Flow.Arith32.mad32_W, PTX.Flow.Arith32.min32_W,
        PTX.Flow.Arith32.shrs_int, PTX.Flow.Arith32.shru_int, PTX.Flow.Arith32.shl8_W,
        PTX.Flow.Arith32.not32_add_W, PTX.Flow.Arith32.scmpi_s_W,
        PTX.Flow.Arith32.scmp_lt_W, PTX.Flow.Arith32.scmp_le_W, PTX.Flow.Arith32.scmp_gt_W,
        PTX.Flow.Arith32.scmp_ge_W, PTX.Flow.Arith32.scmp_ne_b_W, PTX.Flow.Arith32.scmp_eq_b_W,
        PTX.Flow.Arith32.scmpi_eq_b_W, PTX.Flow.Arith32.scmpi_ne_b_W,
        PTX.Flow.Arith32.scmpi_lt_u_W, PTX.Flow.Arith32.scmpi_le_u_W,
        PTX.Flow.Arith32.scmpi_gt_u_W, PTX.Flow.Arith32.scmpi_ge_u_W,
        PTX.Flow.Arith32.scmpi_gt_neg1_W, PTX.Flow.Arith32.i32_int, PTX.Flow.Arith32.r32_W,
        PTX.Flow.Arith32.toNat_W, Int.reduceToNat, Int.toNat_natCast, Nat.reducePow,
        Nat.reduceDiv, Nat.div_eq_of_lt, Nat.zero_div, Nat.add_zero, Nat.zero_add,
        Bool.true_and, Bool.and_true, $ls,*] $[$loc]?)

end

end PTX.Flow.Arith32
