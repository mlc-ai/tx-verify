-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Norm
public import Lemmas.Flow.Arith32WordWide

@[expose] public section

/-! # `w32_norm` with the forms of `Arith32WordWide` (FlashMLA request G17)

`w32k_norm` is `w32_norm` (`Arith32Norm.lean`) with the word forms this library now has beside it:
`and.b32` with `-64`/`-4` (`andi_W_neg64`, `andi_W_neg4`, from `andi_W_neg`), `max.s32` and
`neg.s32` on small words (`Arith32WordWide.lean`'s `max32_W`, `neg32_W`). `w32k_close` closes an
equation of words by it and then by their numbers. Promoted from FlashMLA's `Proof2/Lib/Word.lean`
(lane L2's G17), which also proves the other forms here: the wrapping 32-bit addition and
subtraction (`add32_Wm`, `sub32_Wm`), `addi64`'s equation, the 64-bit shifts and products, and the
bit tests of a low word (`andi_W_low`, `andi_W_31`, `or32_W_64`). -/

namespace PTX.Flow.Arith32
open PTX

noncomputable section

/-- `and.b32` with `-2^k` clears the low `k` bits. -/
theorem andi_W_neg {a k : Nat} (ha : a < 2 ^ 32) (hk : k < 32) :
    andi (W a) (-(2 ^ k : Int)) = W (a - a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ k ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hi : (i32 (-(2 ^ k : Int))).toNat = 2 ^ 32 - 2 ^ k := by
    have hc : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by push_cast; rfl
    rw [hc]
    generalize 2 ^ k = n at hp h1
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  have hm : 2 ^ 32 - 2 ^ k = (2 ^ (32 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_one_mul, ← Nat.pow_add, Nat.sub_add_cancel hk.le]
  simp only [andi, BitVec.toNat_and, r32_W ha, hi, toNat_W (show a < 2 ^ 64 by omega),
    toNat_W (show a - a % 2 ^ k < 2 ^ 64 by omega)]
  rw [hm, ← Nat.shiftLeft_eq, Nat.and_comm]
  have key : ∀ x y : Nat, (x <<< k) &&& y = ((x &&& (y >>> k)) <<< k) := by
    intro x y
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hi : k ≤ i
    · simp [hi, Nat.add_sub_cancel' hi]
    · simp [hi]
  rw [key, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hk.le]; exact ha))]
  have := Nat.div_add_mod a (2 ^ k)
  rw [Nat.mul_comm] at this
  omega

theorem andi_W_neg64 {a : Nat} (ha : a < 2 ^ 32) : andi (W a) (-64) = W (a - a % 64) :=
  andi_W_neg (k := 6) ha (by norm_num)

theorem andi_W_neg4 {a : Nat} (ha : a < 2 ^ 32) : andi (W a) (-4) = W (a - a % 4) :=
  andi_W_neg (k := 2) ha (by norm_num)

/-- The 32-bit additions and subtractions, wrapping. -/
theorem add32_Wm {a b : Nat} : add32 (W a) (W b) = W ((a % 2 ^ 32 + b % 2 ^ 32) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]; omega

theorem sub32_Wm {a b : Nat} :
    sub32 (W a) (W b) = W ((a % 2 ^ 32 + (2 ^ 32 - b % 2 ^ 32)) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_sub]; omega

theorem addi_Wm {a : Nat} {n : Int} (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    addi (W a) n = W ((a % 2 ^ 32 + n.toNat) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]; omega

/-- A 64-bit addition of a nonnegative immediate. -/
theorem addi64_eq (x : BitVec 64) {n : Int} (h : 0 ≤ n) : addi64 x n = x + W n.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-! ### 64-bit and wide forms on small numbers -/

theorem add64_W {a b : Nat} : add64 (W a) (W b) = W (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add64, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]; omega

theorem shl64_2_W {a : Nat} : shl64 (W a) 2 = W (4 * a) := by
  have hi : (i32 (2 : Int)).toNat = 2 := by decide
  simp only [shl64, hi, show ¬ 2 ≥ 64 by omega, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, r64, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem sext_W {a : Nat} (h : a < 2 ^ 31) : sext (W a) = W a := by
  apply BitVec.eq_of_toNat_eq
  have h1 : toSigned 32 (r32 (W a)) = a := by rw [r32_W (by omega)]; exact toSigned_W h
  simp only [sext, cvtIntBits, intBits, intSat, intOf, Bool.not_false, ↓reduceIte]
  rw [h1]
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

theorem mulWide_u_W {a : Nat} {n : Int} (ha : a < 2 ^ 32) (h0 : 0 ≤ n) (hn : n < 2 ^ 31) :
    mulWide .u (W a) n = W (a * n.toNat) := by
  have hi : (i32 n).toNat = n.toNat := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [mulWide, hi, r32_W ha, toNat_W (show a < 2 ^ 64 by omega)]
  rfl

theorem mulWideR_s_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    mulWideR .s (W a) (W b) = W (a * b) := by
  have h1 : toSigned 32 (r32 (W a)) = a := by rw [r32_W (by omega)]; exact toSigned_W ha
  have h2 : toSigned 32 (r32 (W b)) = b := by rw [r32_W (by omega)]; exact toSigned_W hb
  have hab : a * b < 2 ^ 62 := by
    calc a * b < 2 ^ 31 * 2 ^ 31 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 62 := by norm_num
  simp only [mulWideR, h1, h2, beq_self_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  push_cast; omega

/-- Every 64-bit word is the word of its number. -/
theorem eq_W (x : BitVec 64) : x = W x.toNat := by simp [W]

/-- `and.b32` with `2^k - 1` keeps the low `k` bits. -/
theorem andi_W_low {a k : Nat} (ha : a < 2 ^ 32) (hk : k < 31) :
    andi (W a) ((2 ^ k - 1 : Nat) : Int) = W (a % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hp : 2 ^ k < 2 ^ 31 := Nat.pow_lt_pow_right (by norm_num) hk
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hi : (i32 ((2 ^ k - 1 : Nat) : Int)).toNat = 2 ^ k - 1 := by
    generalize 2 ^ k = n at hp h1
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [andi, BitVec.toNat_and, r32_W ha, hi, toNat_W (show a < 2 ^ 64 by omega),
    toNat_W (show a % 2 ^ k < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod]

theorem andi_W_31 {a : Nat} (ha : a < 2 ^ 32) : andi (W a) 31 = W (a % 32) :=
  andi_W_low (k := 5) ha (by norm_num)

/-- `shl.b32` by an immediate below 32, without overflow. -/
theorem shl_W {a k : Nat} (hk : k < 32) (h : a * 2 ^ k < 2 ^ 32) :
    shl (W a) (k : Int) = W (a * 2 ^ k) := by
  have hi : (i32 (k : Int)).toNat = k := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  have ha : a < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_right a Nat.one_le_two_pow) h
  simp only [shl, hi, show ¬ k ≥ 32 by omega, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, r32, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a % 2 ^ 32 < 2 ^ 64 by
    omega), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show a * 2 ^ k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a * 2 ^ k < 2 ^ 64 by omega)]

theorem shl1_W {a : Nat} (h : a * 2 < 2 ^ 32) : shl (W a) 1 = W (a * 2) := shl_W (k := 1) (by
  norm_num) h

/-- `or.b32` of a word below 64 with 64. -/
theorem or32_W_64 {a : Nat} (ha : a < 64) : or32 (W a) (W 64) = W (a + 64) := by
  apply BitVec.eq_of_toNat_eq
  have h : ∀ x < 64, x ||| 64 = x + 64 := by decide
  simp only [or32, BitVec.toNat_or, r32_W (show a < 2 ^ 32 by omega), r32_W (show 64 < 2 ^ 32 by
    omega), toNat_W (show a < 2 ^ 64 by omega), toNat_W (show (64 : Nat) < 2 ^ 64 by omega),
    toNat_W (show a + 64 < 2 ^ 64 by omega), h a ha]

/-- `w32k_norm [lemmas] at loc`: `w32_norm` with this file's forms. -/
syntax "w32k_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic

macro_rules
  | `(tactic| w32k_norm $[$loc]?) => `(tactic| w32k_norm [] $[$loc]?)
  | `(tactic| w32k_norm [$ls,*] $[$loc]?) => `(tactic|
      w32_norm [PTX.Flow.Arith32.andi_W_neg64, PTX.Flow.Arith32.andi_W_neg4,
        PTX.Flow.Arith32.max32_W, PTX.Flow.Arith32.neg32_W, $ls,*] $[$loc]?)

/-- Close an equation of words by `w32k_norm`, then by the equation of their numbers. -/
macro "w32k_close" : tactic => `(tactic| first
  | (w32k_norm; done)
  | (w32k_norm; congr 1 <;> omega)
  | (congr 1 <;> omega))

end

end PTX.Flow.Arith32
