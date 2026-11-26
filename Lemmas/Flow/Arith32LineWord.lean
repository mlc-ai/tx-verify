-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Arith32Interval

@[expose] public section

/-! # The swizzled address of a 16-byte column in its line (library candidate)

`Col a i k x`: the word `x` is the address of the 16-byte column `(i mod 8) xor k` of the 128-byte
line at `a`. The swizzle of a line whose number has the low bits of `i` is column 0's (`col_swz`),
and the signed moves by 16, 32 and 64, chosen by the bits of `i`, flip the bits of `k`
(`col_d1`, `col_d2`, `col_d4`). So the address the code computes for a column is exact. -/

namespace PTX.Flow.Arith32
open PTX

/-- The word `x` is the address of column `(i mod 8) xor k` of the line at `a`. -/
def Col (a i k : Nat) (x : BitVec 64) : Prop := x.toNat = a + 16 * ((i % 8) ^^^ k)

theorem col_xor_lt : ∀ a < 8, ∀ b < 8, a ^^^ b < 8 := by decide

theorem Col.bounds {a i k : Nat} {x : BitVec 64} (h : Col a i k x) (hk : k < 8) :
    a ≤ x.toNat ∧ x.toNat + 16 ≤ a + 128 := by
  have := col_xor_lt (i % 8) (by omega) k hk
  unfold Col at h
  omega

theorem and_112 (n : Nat) : 16 * n &&& 112 = 16 * (n % 8) := by
  have h := Nat.shiftLeft_and_distrib (a := n) (b := 7) (i := 4)
  rw [show (7 : Nat) = 2 ^ 3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
  simp only [Nat.shiftLeft_eq] at h
  norm_num at h
  rw [Nat.mul_comm 16 n, ← h, Nat.mul_comm]

theorem xor_line {M n : Nat} (hM : M < 128) : M ^^^ 128 * n = 128 * n + M := by
  have h1 : (M ^^^ 128 * n) / 128 = n := by
    rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.xor_div_two_pow, Nat.div_eq_of_lt (by omega),
      Nat.zero_xor]
    omega
  have h2 : (M ^^^ 128 * n) % 128 = M := by
    have h := @Nat.xor_mod_two_pow M (128 * n) 7
    norm_num at h
    rw [h, Nat.mod_eq_of_lt hM]
  omega

theorem toNat_i32_neg {n : Nat} (hn : 0 < n) (h : n < 2 ^ 31) :
    (i32 (-(n : Int))).toNat = 2 ^ 32 - n := by
  simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- **The swizzle of the address of line `n`** (counted from a 1024-aligned base) is the address
of its column `n mod 8`. -/
theorem col_swz {x : BitVec 64} {n i : Nat} (hx : x.toNat = 128 * n) (hn : 128 * n < 2 ^ 32)
    (hi : n % 8 = i % 8) : Col (128 * n) i 0 (xor32 (andi (shru x 3) 112) x) := by
  have h112 := toNat_i32 112 (by omega)
  have hs : (shru x 3).toNat = 16 * n := by
    have h := iv_shru (x := x) (a := 128 * n) (b := 128 * n) ⟨hx.ge, hx.le⟩ 3 (by decide) hn
    unfold Iv at h
    norm_num at h
    omega
  have ha : (andi (shru x 3) 112).toNat = 16 * (n % 8) := by
    simp only [andi, BitVec.toNat_and, Nat.cast_ofNat] at h112 ⊢
    rw [h112, toNat_r32, hs, Nat.mod_eq_of_lt (by omega), and_112]
  unfold Col
  simp only [xor32, BitVec.toNat_xor, toNat_r32, ha, hx]
  rw [Nat.mod_eq_of_lt (a := 16 * (n % 8)) (by omega), Nat.mod_eq_of_lt hn,
    xor_line (by omega), Nat.xor_zero, hi]

theorem col_flip : ∀ a : Fin 8, ∀ k : Fin 8, ∀ s : Fin 3, k.val / 2 ^ s.val % 2 = 0 →
    (a.val / 2 ^ s.val % 2 = 0 → a.val ^^^ (k.val ^^^ 2 ^ s.val) =
      (a.val ^^^ k.val) + 2 ^ s.val ∧
      (a.val ^^^ k.val) + 2 ^ s.val < 8) ∧
    (a.val / 2 ^ s.val % 2 = 1 → (a.val ^^^ (k.val ^^^ 2 ^ s.val)) + 2 ^ s.val =
      a.val ^^^ k.val) := by
  decide

/-- **A signed move by `16 · 2 ^ s`, chosen by bit `s` of `i`, flips bit `s` of the column.** -/
theorem col_move {a i k s : Nat} {x : BitVec 64} {c : Bool} (h : Col a i k x)
    (hk : k < 8) (hs : s < 3) (hb : k / 2 ^ s % 2 = 0) (ha : a + 128 < 2 ^ 32)
    (hc : c = decide (i / 2 ^ s % 2 = 0)) :
    Col a i (k ^^^ 2 ^ s) (add32 x
      (sel c (i32 ((16 * 2 ^ s : Nat) : Int)) (i32 (-((16 * 2 ^ s : Nat) : Int))))) := by
  obtain ⟨e1, e2⟩ := col_flip ⟨i % 8, by omega⟩ ⟨k, hk⟩ ⟨s, hs⟩ hb
  simp only at e1 e2
  have h3 : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  have hbit : i % 8 / 2 ^ s % 2 = i / 2 ^ s % 2 := by
    rcases h3 with rfl | rfl | rfl <;> norm_num <;> omega
  rw [hbit] at e1 e2
  have hlt := col_xor_lt (i % 8) (by omega) k hk
  have h16 : 16 * 2 ^ s ≤ 64 := by rcases h3 with rfl | rfl | rfl <;> norm_num
  have h16' : 0 < 16 * 2 ^ s := Nat.mul_pos (by decide) (Nat.two_pow_pos s)
  unfold Col at h ⊢
  subst hc
  by_cases hi : i / 2 ^ s % 2 = 0
  · obtain ⟨e, e'⟩ := e1 hi
    have hp := iv_add32 (x := x) (a := x.toNat) (b := x.toNat) ⟨le_rfl, le_rfl⟩
      (iv_i32 (16 * 2 ^ s) (by omega)) (by omega)
    unfold Iv at hp
    simp only [hi, decide_true, sel, ↓reduceIte]
    omega
  · have e := e2 (by omega)
    have hge : 16 * 2 ^ s ≤ x.toNat := by omega
    have hp := iv_add32_neg (x := x) (a := x.toNat) (b := x.toNat) ⟨le_rfl, le_rfl⟩ (16 * 2 ^ s)
      hge (by omega)
    unfold Iv at hp
    simp only [hi, decide_false, sel, Bool.false_eq_true, ↓reduceIte]
    omega

theorem tr32 (z : BitVec 64) : (truncBits 32 z).toNat = z.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem xor16_table : ∀ a < 8, ∀ b < 8, (a * 16) ^^^ (b * 16) ≤ 112 ∧
    ((a * 16) ^^^ (b * 16)) % 16 = 0 := by decide

/-- **The swizzle keeps a 16-byte-aligned word in its 128-byte line, 16-byte aligned, at most
112 bytes into the line.** -/
theorem swz_line (x : BitVec 64) (h16 : x.toNat % 16 = 0) (hx : x.toNat < 2 ^ 32) :
    (xor32 (andi (shru x 3) 112) x).toNat / 128 = x.toNat / 128 ∧
      (xor32 (andi (shru x 3) 112) x).toNat % 128 ≤ 112 ∧
      (xor32 (andi (shru x 3) 112) x).toNat % 16 = 0 := by
  have hi : (i32 112).toNat = 112 := by
    simp only [i32, tr32, BitVec.toNat_ofInt]; norm_num
  simp only [xor32, andi, r32, tr32, BitVec.toNat_xor, BitVec.toNat_and, hi]
  rw [Nat.mod_eq_of_lt hx]
  generalize (shru x 3).toNat = A
  have hM : (A % 2 ^ 32 &&& 112) % 2 ^ 32 = A % 2 ^ 32 &&& 112 :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right (by norm_num))
  rw [hM]
  generalize hMd : A % 2 ^ 32 &&& 112 = M
  have hM1 : M ≤ 112 := hMd ▸ Nat.and_le_right
  have hM2 : M % 16 = 0 := by
    rw [← hMd, show (16 : Nat) = 2 ^ 4 by norm_num, Nat.and_mod_two_pow]
    simp
  generalize hX : x.toNat = X at *
  refine ⟨?_, ?_⟩
  · rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.xor_div_two_pow,
      Nat.div_eq_of_lt (show M < 2 ^ 7 by omega), Nat.zero_xor]
  have hmod : (M ^^^ X) % 128 = M ^^^ (X % 128) := by
    rw [show (128 : Nat) = 2 ^ 7 by norm_num, Nat.xor_mod_two_pow,
      Nat.mod_eq_of_lt (show M < 2 ^ 7 by omega)]
  have e1 : M = M / 16 * 16 := by omega
  have e2 : X % 128 = X % 128 / 16 * 16 := by omega
  have ht := xor16_table (M / 16) (by omega) (X % 128 / 16) (by omega)
  rw [← e1, ← e2] at ht
  refine ⟨by rw [hmod]; exact ht.1, ?_⟩
  have : (M ^^^ X) % 16 = (M ^^^ X) % 128 % 16 := by omega
  rw [this, hmod, ht.2]

theorem and_112_div (A : Nat) : A &&& 112 = 16 * (A / 16 % 8) := by
  have h1 : (A &&& 112) % 16 = 0 := by
    rw [show (16 : Nat) = 2 ^ 4 by norm_num, Nat.and_mod_two_pow]
    simp
  have h2 : (A &&& 112) / 16 = A / 16 % 8 := by
    rw [show (16 : Nat) = 2 ^ 4 by norm_num, Nat.and_div_two_pow,
      show (112 : Nat) / 2 ^ 4 = 2 ^ 3 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem xor_col : ∀ a < 8, ∀ c < 8, (16 * a) ^^^ (16 * c) = 16 * (c ^^^ a) := by decide

/-- **The swizzle of the address of column `c` of line `n`** is the address of column
`c xor (n mod 8)` of the line. -/
theorem swz_val {x : BitVec 64} {n c : Nat} (hx : x.toNat = 128 * n + 16 * c) (hc : c < 8)
    (hn : 128 * n + 128 < 2 ^ 32) :
    (xor32 (andi (shru x 3) 112) x).toNat = 128 * n + 16 * (c ^^^ (n % 8)) := by
  obtain ⟨e1, -, -⟩ := swz_line x (by omega) (by omega)
  have h112 := toNat_i32 112 (by omega)
  have hs : (shru x 3).toNat = 16 * n + 2 * c := by
    have h := iv_shru (x := x) (a := x.toNat) (b := x.toNat) ⟨le_rfl, le_rfl⟩ 3 (by decide)
      (by omega)
    unfold Iv at h
    norm_num at h
    omega
  have ha : (andi (shru x 3) 112).toNat = 16 * (n % 8) := by
    simp only [andi, BitVec.toNat_and, Nat.cast_ofNat] at h112 ⊢
    rw [h112, toNat_r32, hs, Nat.mod_eq_of_lt (by omega), and_112_div]
    omega
  have hm : (xor32 (andi (shru x 3) 112) x).toNat % 128 = 16 * (c ^^^ (n % 8)) := by
    simp only [xor32, BitVec.toNat_xor, toNat_r32, ha, hx]
    rw [Nat.mod_eq_of_lt (a := 16 * (n % 8)) (by omega),
      Nat.mod_eq_of_lt (a := 128 * n + 16 * c) (by omega)]
    have h := @Nat.xor_mod_two_pow (16 * (n % 8)) (128 * n + 16 * c) 7
    norm_num at h
    rw [h, Nat.mod_eq_of_lt (a := 16 * (n % 8)) (by omega),
      Nat.mod_eq_of_lt (a := 16 * c) (by omega)]
    exact xor_col _ (by omega) _ hc
  omega

end PTX.Flow.Arith32
