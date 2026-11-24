-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Step.SegSym

@[expose] public section

/-! # The code's 32-bit arithmetic on small words

A proof tool (promoted from the tml-fa4 output warp's proof; a module of its own beside
`Lemmas/Flow/Arith32.lean` because it needs `Flow.divQ` from `Step/SegSym.lean`). On words
whose values stay below `2 ^ 31` (`W n`), the operations of the code's vocabulary
(`Lemmas/Flow/Arith32.lean`) are the operations on natural numbers: additions, subtractions,
products, shifts, the signed comparisons, the minimum, the population count, and the signed
division with the floor quotient the code builds from it (`sdiv`, `divOk`, `fdiv`). -/

namespace PTX.Flow.Arith32
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A signed 32-bit division, and whether the code's `div.s32` has a rule for it (a nonzero
divisor, an exact quotient when the signs differ, no overflow). -/
def sdiv (x y : BitVec 64) : BitVec 64 := Flow.divQ .s 32 (r32 x) (r32 y)
def divOk (x y : BitVec 64) : Bool := Flow.divOk .s 32 (r32 x) (r32 y)

/-- The floor quotient the code builds from `div.s32`. -/
abbrev fdiv (x y : BitVec 64) : BitVec 64 :=
  add32 (sdiv x y) (sel (scmp .ne .b x (mul32 y (sdiv x y)) && scmpi .lt .s (xor32 y x) 0)
    (i32 (-1)) (i32 0))

/-- A word below `2 ^ 31`. -/
abbrev W (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

theorem toNat_W {n : Nat} (h : n < 2 ^ 64) : (W n).toNat = n := by
  simp only [W, BitVec.toNat_ofNat]; omega

theorem r32_W {n : Nat} (h : n < 2 ^ 32) : r32 (W n) = W n := by
  apply BitVec.eq_of_toNat_eq
  simp only [r32, truncBits, W, BitVec.toNat_ofNat]; omega

theorem i32_W {n : Nat} (h : n < 2 ^ 31) : i32 (n : Int) = W n := by
  apply BitVec.eq_of_toNat_eq
  simp only [i32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega

theorem add32_W {a b : Nat} (h : a + b < 2 ^ 32) : add32 (W a) (W b) = W (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [add32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add]; omega

theorem addi_W {a : Nat} {n : Nat} (hn : n < 2 ^ 31) (h : a + n < 2 ^ 32) :
    addi (W a) (n : Int) = W (a + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]; omega

theorem addi31_W {a : Nat} (h : a + 31 < 2 ^ 32) : addi (W a) 31 = W (a + 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]; omega

theorem addi1_W {a : Nat} (h : a + 1 < 2 ^ 32) : addi (W a) 1 = W (a + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]; omega

theorem i32_zero : i32 0 = W 0 := rfl

/-- The signed comparison of two words below `2 ^ 31` is the comparison of their values. -/
theorem scmp_W (c : Cmp) {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    scmp c .s (W a) (W b) = PTX.compare c .s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) := by
  rw [scmp, r32_W (by omega), r32_W (by omega)]

theorem toSigned_W {a : Nat} (ha : a < 2 ^ 31) : toSigned 32 (BitVec.ofNat 64 a) = a := by
  have h1 : (BitVec.ofNat 64 a).toNat = a := by simp only [BitVec.toNat_ofNat]; omega
  simp only [toSigned, h1]
  have h2 : a % 4294967296 = a := by omega
  have h3 : a < 2147483648 := by omega
  simp only [Nat.reduceSub, Nat.reducePow, h2, h3, ↓reduceIte]

theorem scmp_lt_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    scmp .lt .s (W a) (W b) = decide (a < b) := by
  rw [scmp_W _ ha hb]
  simp [PTX.compare, toSigned_W ha, toSigned_W hb]

theorem scmp_le_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    scmp .le .s (W a) (W b) = decide (a ≤ b) := by
  rw [scmp_W _ ha hb]
  simp [PTX.compare, toSigned_W ha, toSigned_W hb]

theorem scmp_gt_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    scmp .gt .s (W a) (W b) = decide (b < a) := by
  rw [scmp_W _ ha hb]
  simp [PTX.compare, toSigned_W ha, toSigned_W hb]

theorem scmp_ge_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    scmp .ge .s (W a) (W b) = decide (b ≤ a) := by
  rw [scmp_W _ ha hb]
  simp [PTX.compare, toSigned_W ha, toSigned_W hb]

theorem min32_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    min32 (W a) (W b) = W (min a b) := by
  have hl : compare .lt .s 32 (W a) (W b) = decide (a < b) := by
    have := scmp_lt_W ha hb
    simpa [scmp, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega)] using this
  simp only [min32, r32_W (show a < 2 ^ 32 by omega), r32_W (show b < 2 ^ 32 by omega), hl]
  by_cases h : a < b
  · simp only [h, decide_true, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt h)]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte,
      Nat.min_eq_right (Nat.le_of_not_lt h)]

theorem sub32_W {a b : Nat} (hab : b ≤ a) (ha : a < 2 ^ 32) : sub32 (W a) (W b) = W (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sub32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_sub]; omega

theorem mul32_W {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a * b < 2 ^ 32) :
    mul32 (W a) (W b) = W (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [mul32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_mul]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a * b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a * b < 2 ^ 64 by omega)]

theorem mad32_W {a b c : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a * b + c < 2 ^ 32) :
    mad32 (W a) (W b) (W c) = W (a * b + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [mad32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_add]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (show c < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a * b < 2 ^ 64 by omega)]
  omega

theorem toNat_shrs_W {a : Nat} (ha : a < 2 ^ 31) {k : Nat} (hk : k < 32) :
    shrs (W a) (k : Int) = W (a / 2 ^ k) := by
  have h1 : toSigned 32 (r32 (W a)) = a := by rw [r32_W (by omega)]; exact toSigned_W ha
  have h2 : (i32 (k : Int)).toNat = k := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [shrs]
  rw [h1, h2]
  rw [Nat.min_eq_left (show k ≤ 32 by omega)]
  have h3 : ((a : Int) / 2 ^ k) = ((a / 2 ^ k : Nat) : Int) := by norm_cast
  rw [h3, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  have hd : a / 2 ^ k ≤ a := Nat.div_le_self _ _
  simp only [truncBits, W, BitVec.toNat_ofNat]
  generalize a / 2 ^ k = q at hd ⊢
  omega

theorem scmp_ne_b_W {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    scmp .ne .b (W a) (W b) = decide (a ≠ b) := by
  simp only [scmp, r32_W ha, r32_W hb, PTX.compare, W, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  simp

theorem scmpi_gt_neg1_W {a : Nat} (ha : a < 2 ^ 31) : scmpi .gt .s (W a) (-1) = true := by
  have hm : toSigned 32 (i32 (-1)) = -1 := by decide
  simp only [scmpi, PTX.compare, r32_W (show a < 2 ^ 32 by omega), toSigned_W ha, hm]
  simp; omega

theorem shl8_W {a : Nat} (h : a * 256 < 2 ^ 32) : shl (W a) 8 = W (256 * a) := by
  have hi : (i32 (8 : Int)).toNat = 8 := by decide
  simp only [shl]
  rw [hi]
  split_ifs with h8
  · exact absurd h8 (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, r32, W, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
  rw [Nat.shiftLeft_eq]
  have ha : a < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show a % 2 ^ 32 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt ha]
  omega

theorem not32_add_W {n q : Nat} (hq : q < n) (hn : n < 2 ^ 31) :
    add32 (W n) (not32 (W q)) = W (n - 1 - q) := by
  apply BitVec.eq_of_toNat_eq
  have hq' : q < 2 ^ 32 := by omega
  simp only [add32, not32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_not]
  rw [Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hq', Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)]
  omega

theorem sdiv_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (hb0 : 0 < b) :
    sdiv (W a) (W b) = W (a / b) ∧ divOk (W a) (W b) = true := by
  have hia : intOf .s 32 (r32 (W a)) = a := by
    simp only [intOf, ↓reduceIte]; rw [r32_W (by omega)]; exact toSigned_W ha
  have hib : intOf .s 32 (r32 (W b)) = b := by
    simp only [intOf, ↓reduceIte]; rw [r32_W (by omega)]; exact toSigned_W hb
  have hdiv : intDiv .s 32 (r32 (W a)) (r32 (W b)) = .ok ((a / b : Nat) : Int) := by
    have hq : (a : Int).tdiv b = ((a / b : Nat) : Int) := by
      rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; norm_cast
    have hle : a / b ≤ a := Nat.div_le_self _ _
    have hab : ¬ (((a : Int).tmod b ≠ 0) ∧ (((a : Int) < 0) ≠ ((b : Int) < 0))) := by
      rintro ⟨-, h⟩
      apply h
      rw [eq_false (show ¬ ((a : Int) < 0) by omega), eq_false (show ¬ ((b : Int) < 0) by omega)]
    simp only [intDiv, hia, hib, hq, bind, Except.bind, pure, Except.pure]
    split_ifs <;> first | rfl | (exfalso; omega)
  refine ⟨?_, ?_⟩
  · simp only [sdiv, Flow.divQ, hdiv, intBits, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    have hle : a / b ≤ a := Nat.div_le_self _ _
    simp only [truncBits, W, BitVec.toNat_ofNat]
    generalize a / b = q at hle ⊢
    omega
  · simp only [divOk, Flow.divOk, hdiv]

theorem fdiv_W {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (hb0 : 0 < b) :
    fdiv (W a) (W b) = W (a / b) := by
  obtain ⟨hs, -⟩ := sdiv_W ha hb hb0
  have hle : a / b ≤ a := Nat.div_le_self _ _
  have hm : b * (a / b) ≤ a := Nat.mul_div_le a b
  have hx : scmpi .lt .s (xor32 (W b) (W a)) 0 = false := by
    have hx' : xor32 (W b) (W a) = W (b ^^^ a) := by
      apply BitVec.eq_of_toNat_eq
      simp only [xor32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_xor]
      rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
      have : b ^^^ a < 2 ^ 31 := Nat.xor_lt_two_pow hb ha
      omega
    have hlt : b ^^^ a < 2 ^ 31 := Nat.xor_lt_two_pow hb ha
    have h0 : toSigned 32 (i32 0) = 0 := by decide
    simp only [scmpi, PTX.compare, hx', r32_W (show b ^^^ a < 2 ^ 32 by omega), toSigned_W hlt, h0]
    simp
  simp only [fdiv, hs, hx, Bool.and_false, sel, Bool.false_eq_true, ↓reduceIte, i32_zero]
  rw [add32_W (by omega)]
  simp

theorem popc_W (x : BitVec 64) : ∃ n ≤ 32, popc x = W n := by
  refine ⟨_, ?_, rfl⟩
  calc ((List.range 32).filter (r32 x).toNat.testBit).length ≤ (List.range 32).length :=
        List.length_filter_le _ _
    _ = 32 := List.length_range

end
end PTX.Flow.Arith32
