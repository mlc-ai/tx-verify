-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Arith.FastDivmod

@[expose] public section

/-!
# Signed ceiling division by a power of two

Compilers lower `ceil_div(x, 2^k)` on a signed 32-bit `x` (C's `(x + 2^k - 1) / 2^k` with
truncating division, or a signed `x / 2^k` rounded up) to a branch-free sequence:
```
shr.s32  s, x, 31          // 0 or -1: the sign of x
shr.u32  f, s, 32-k        // 0 or 2^k - 1: the rounding fix-up for negative x
add.s32  y, x, f
shr.s32  q, y, k           // x / 2^k, rounded toward zero
and.b32  r, y, -2^k        // y with the low k bits cleared
setp.ne.b32  p1, x, r      // x is not a multiple of 2^k (for x ≥ 0)
setp.gt.s32  p2, x, -1     // x ≥ 0
and.pred     p, p2, p1
selp.b32     c, 1, 0, p
add.s32      n, q, c       // q + 1 when x > 0 is not a multiple of 2^k
```
(the order of the independent instructions varies between instances). `ceilShr k x` is this
sequence on 32-bit words, each instruction modelled as the core's integer rules compute it
(THREAD-INT: wraparound, two's complement for `.s32`, floor division for an arithmetic shift).
For `0 ≤ x < 2^31` and `k ≤ 31` it is `(x + 2^k - 1) / 2^k` (`ceilShr_eq`); the intermediate
values are stated on their own (`ceilShr_quot`, `ceilShr_pred`), for proofs that cut the
sequence at the `selp`, whose predicate the evaluation of a segment cannot decide.
-/

namespace CeilDiv

open FastDivmod (W add32 shr32)

/-- The two's complement value of a 32-bit word. -/
def toInt32 (a : Nat) : Int := if a % W < 2 ^ 31 then ((a % W : Nat) : Int) else (a % W : Nat) - W

/-- The 32-bit word of an integer. -/
def ofInt32 (i : Int) : Nat := (i % (W : Int)).toNat

/-- `shr.s32`: arithmetic right shift, the amount clamped to 32. -/
def sshr32 (a s : Nat) : Nat := ofInt32 (toInt32 a / 2 ^ min s 32)

/-- `and.b32`. -/
def and32 (a b : Nat) : Nat := a % W &&& b % W

/-- The `.s32` comparison `a > b` of `setp.gt.s32`. -/
def sgt32 (a b : Nat) : Bool := decide (toInt32 a > toInt32 b)

/-- The `.b32` comparison `a ≠ b` of `setp.ne.b32`. -/
def ne32 (a b : Nat) : Bool := decide (a % W ≠ b % W)

/-- The rounding predicate `x > -1 ∧ x ≠ r` of the sequence. -/
def ceilPred (k x : Nat) : Bool :=
  let y := add32 x (shr32 (sshr32 x 31) (32 - k))
  sgt32 x (W - 1) && ne32 x (and32 y (W - 2 ^ k))

/-- The rounded-toward-zero quotient `q` of the sequence. -/
def ceilQuot (k x : Nat) : Nat := sshr32 (add32 x (shr32 (sshr32 x 31) (32 - k))) k

/-- The whole sequence: `q + (p ? 1 : 0)`. -/
def ceilShr (k x : Nat) : Nat := add32 (ceilQuot k x) (if ceilPred k x then 1 else 0)

/-- The bits `k … n-1` of `a`: `a &&& (2^n - 2^k)` clears the bits below `k` and from `n`. -/
theorem land_highMask (a n k : Nat) (hk : k ≤ n) :
    a &&& (2 ^ n - 2 ^ k) = a % 2 ^ n / 2 ^ k * 2 ^ k := by
  have hm : 2 ^ n - 2 ^ k = (2 ^ (n - k) - 1) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
  rw [hm, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases hi : k ≤ i
  · have : k + (i - k) = i := by omega
    simp only [ge_iff_le, hi, decide_true, Bool.true_and, this]
    by_cases hn : i < n
    · simp [hn, show i - k < n - k by omega]
    · simp [hn, show ¬ i - k < n - k by omega]
  · simp [hi]

theorem toInt32_of_lt {a : Nat} (ha : a < 2 ^ 31) : toInt32 a = a := by
  have : a % W = a := Nat.mod_eq_of_lt (by unfold W; omega)
  simp only [toInt32, this, ha, ↓reduceIte]

theorem ofInt32_natCast {a : Nat} (ha : a < W) : ofInt32 a = a := by
  unfold ofInt32
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

/-- An arithmetic shift of a nonnegative word is a division. -/
theorem sshr32_of_lt {a s : Nat} (ha : a < 2 ^ 31) (hs : s ≤ 32) : sshr32 a s = a / 2 ^ s := by
  unfold sshr32
  rw [toInt32_of_lt ha, Nat.min_eq_left hs]
  have hW : a / 2 ^ s < W := lt_of_le_of_lt (Nat.div_le_self _ _) (by unfold W; omega)
  rw [show (a : Int) / 2 ^ s = ((a / 2 ^ s : Nat) : Int) by push_cast; rfl, ofInt32_natCast hW]

/-- The quotient of the sequence, for a nonnegative `x`. -/
theorem ceilQuot_eq {k x : Nat} (hk : k ≤ 31) (hx : x < 2 ^ 31) : ceilQuot k x = x / 2 ^ k := by
  have hW : x < W := by unfold W; omega
  unfold ceilQuot
  rw [sshr32_of_lt hx (by omega), Nat.div_eq_of_lt hx, show shr32 0 (32 - k) = 0 by simp [shr32],
    show add32 x 0 = x by simp [add32, Nat.mod_eq_of_lt hW], sshr32_of_lt hx (by omega)]

/-- The rounding predicate of the sequence, for a nonnegative `x`: `x` is not a multiple of
`2^k`. -/
theorem ceilPred_eq {k x : Nat} (hk : k ≤ 31) (hx : x < 2 ^ 31) :
    ceilPred k x = decide (x % 2 ^ k ≠ 0) := by
  have hW : x < W := by unfold W; omega
  have hpk : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) hk
  have hmask : (W - 2 ^ k) % W = 2 ^ 32 - 2 ^ k :=
    Nat.mod_eq_of_lt (by unfold W; have := Nat.two_pow_pos k; omega)
  have hm1 : toInt32 (W - 1) = -1 := by simp [toInt32, W]
  have hsgt : sgt32 x (W - 1) = true := by
    simp only [sgt32, toInt32_of_lt hx, hm1, decide_eq_true_eq]
    omega
  have hy : add32 x (shr32 (sshr32 x 31) (32 - k)) = x := by
    rw [sshr32_of_lt hx (by omega), Nat.div_eq_of_lt hx]
    simp [shr32, add32, Nat.mod_eq_of_lt hW]
  have hand : and32 x (W - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
    unfold and32
    have hW' : x < 2 ^ 32 := hW
    rw [hmask, land_highMask _ 32 k (by omega), Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hW']
  unfold ceilPred
  simp only [hy, hsgt, Bool.true_and, ne32, hand]
  have hlt : x / 2 ^ k * 2 ^ k < W := lt_of_le_of_lt (Nat.div_mul_le_self _ _) hW
  rw [Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hlt]
  have h := Nat.div_add_mod x (2 ^ k)
  rw [Nat.mul_comm] at h
  generalize x / 2 ^ k * 2 ^ k = m at h ⊢
  simp only [decide_eq_decide]
  omega

/-- **The ceiling.** For `0 ≤ x < 2^31` the sequence computes `⌈x / 2^k⌉`. -/
theorem ceilShr_eq {k x : Nat} (hk : k ≤ 31) (hx : x < 2 ^ 31) :
    ceilShr k x = (x + 2 ^ k - 1) / 2 ^ k := by
  have hd : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq : x / 2 ^ k + 1 < W := by
    have : x / 2 ^ k ≤ x := Nat.div_le_self _ _
    unfold W; omega
  have key : (x + 2 ^ k - 1) / 2 ^ k = x / 2 ^ k + if x % 2 ^ k = 0 then 0 else 1 := by
    generalize 2 ^ k = d at hd ⊢
    have h1 := Nat.div_add_mod x d
    have h2 := Nat.mod_lt x hd
    generalize x / d = q at h1 ⊢
    generalize x % d = r at h1 h2 ⊢
    subst h1
    have e1 : (q + 1) * d = d * q + d := by ring
    have e2 : (q + 1 + 1) * d = d * q + d + d := by ring
    split_ifs with h
    · subst h
      simp only [add_zero]
      exact Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by omega)
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  unfold ceilShr add32
  rw [ceilQuot_eq hk hx, ceilPred_eq hk hx, key]
  by_cases h : x % 2 ^ k = 0 <;> simp only [h, ne_eq, not_true_eq_false, not_false_eq_true,
    decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true] <;>
    exact Nat.mod_eq_of_lt (by omega)

end CeilDiv
