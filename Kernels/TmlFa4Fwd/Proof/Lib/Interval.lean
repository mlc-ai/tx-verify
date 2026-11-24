-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32

@[expose] public section

/-! # Intervals of the code's 32-bit words (library candidate)

`Iv lo hi x`: the word `x` lies in `[lo, hi]`. The rules compute the interval of a term of the
code's 32-bit arithmetic (`Lemmas/Flow/Arith32.lean`) from the intervals of its operands, forward:
a sum without wrap (`iv_add32`, `iv_addi`, and `iv_addi_neg` for a negative immediate), a left
shift without overflow, a right shift, an `and` with an immediate, an `or`, a choice, and an
exclusive or with a bounded word (`iv_xor32`: `x ^^^ m` is within `m` of `x`, since
`x ^^^ m + 2 (x &&& m) = x + m`). The swizzle of a shared address,
`xor32 (andi (shru x 3) 112) x`, moves it by at most 112 (`iv_swz`). Every bound is a term the rule
builds from its operands' bounds; the side conditions are small linear facts about literals and
the launch's shared base, which the caller closes (`omega`, `decide`), so no search runs over the
address term. `eff_shared` reads a shared effective address (a 32-bit word plus an offset,
truncated to 32 bits) as the plain sum when it does not wrap. -/

namespace PTX.Flow.Arith32
open PTX

/-- The word `x` lies in `[lo, hi]`. -/
def Iv (lo hi : Nat) (x : BitVec 64) : Prop := lo ≤ x.toNat ∧ x.toNat ≤ hi

/-! ### Bitwise facts on naturals -/

theorem nat_xor_add_and (x y : Nat) : (x ^^^ y) + 2 * (x &&& y) = x + y := by
  induction x using Nat.strongRecOn generalizing y with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h1 := ih (x / 2) (Nat.div_lt_self hx (by decide)) (y / 2)
      have hx2 := Nat.div_add_mod x 2
      have hy2 := Nat.div_add_mod y 2
      have hxor : x ^^^ y = 2 * (x / 2 ^^^ y / 2) + (x ^^^ y) % 2 := by
        rw [← Nat.xor_div_two]; exact (Nat.div_add_mod _ 2).symm
      have hand : x &&& y = 2 * (x / 2 &&& y / 2) + (x &&& y) % 2 := by
        rw [← Nat.and_div_two]; exact (Nat.div_add_mod _ 2).symm
      have ha : (x &&& y) % 2 = (x % 2) &&& (y % 2) := Nat.and_mod_two_pow (n := 1)
      have hb : (x ^^^ y) % 2 = (x % 2) ^^^ (y % 2) := Nat.xor_mod_two_pow (n := 1)
      have key : (x % 2 ^^^ y % 2) + 2 * (x % 2 &&& y % 2) = x % 2 + y % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
          rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> rw [h, h'] <;> rfl
      rw [hxor, hand, ha, hb]
      omega

theorem nat_or_add_and (x y : Nat) : (x ||| y) + (x &&& y) = x + y := by
  induction x using Nat.strongRecOn generalizing y with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have h1 := ih (x / 2) (Nat.div_lt_self hx (by decide)) (y / 2)
      have hx2 := Nat.div_add_mod x 2
      have hy2 := Nat.div_add_mod y 2
      have hor : x ||| y = 2 * (x / 2 ||| y / 2) + (x ||| y) % 2 := by
        rw [← Nat.or_div_two]; exact (Nat.div_add_mod _ 2).symm
      have hand : x &&& y = 2 * (x / 2 &&& y / 2) + (x &&& y) % 2 := by
        rw [← Nat.and_div_two]; exact (Nat.div_add_mod _ 2).symm
      have ha : (x &&& y) % 2 = (x % 2) &&& (y % 2) := Nat.and_mod_two_pow (n := 1)
      have hb : (x ||| y) % 2 = (x % 2) ||| (y % 2) := Nat.or_mod_two_pow (n := 1)
      have key : (x % 2 ||| y % 2) + (x % 2 &&& y % 2) = x % 2 + y % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
          rcases Nat.mod_two_eq_zero_or_one y with h' | h' <;> rw [h, h'] <;> rfl
      rw [hor, hand, ha, hb]
      omega

/-! ### The rules -/

variable {a b c d : Nat} {x y : BitVec 64}

theorem iv_mono {a' b' : Nat} (ha : a' ≤ a) (hb : b ≤ b') (h : Iv a b x) : Iv a' b' x :=
  ⟨ha.trans h.1, h.2.trans hb⟩

theorem iv_lit (n : Nat) (h : n < 2 ^ 64) : Iv n n (BitVec.ofNat 64 n) := by
  unfold Iv; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; omega

theorem toNat_r32 (x : BitVec 64) : (r32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem iv_r32 (h : Iv a b x) (hb : b < 2 ^ 32) : Iv a b (r32 x) := by
  unfold Iv at *; rw [toNat_r32, Nat.mod_eq_of_lt (by omega)]; exact h

theorem toNat_i32 (n : Nat) (h : n < 2 ^ 32) : (i32 n).toNat = n := by
  simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have h1 : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n := by omega
  rw [h1]; omega

theorem iv_i32 (n : Nat) (h : n < 2 ^ 32) : Iv n n (i32 n) := by
  unfold Iv; rw [toNat_i32 n h]; omega

theorem toNat_tb_add (u v : BitVec 64) :
    (truncBits 32 (u + v)).toNat = (u.toNat + v.toNat) % 2 ^ 64 % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem iv_add32 (hx : Iv a b x) (hy : Iv c d y) (h : b + d < 2 ^ 32) :
    Iv (a + c) (b + d) (add32 x y) := by
  unfold Iv at *
  show a + c ≤ (truncBits 32 (r32 x + r32 y)).toNat ∧ (truncBits 32 (r32 x + r32 y)).toNat ≤ b + d
  rw [toNat_tb_add, toNat_r32, toNat_r32, Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat) (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem iv_addi (hx : Iv a b x) (n : Nat) (h : b + n < 2 ^ 32) :
    Iv (a + n) (b + n) (addi x n) := by
  have hn := toNat_i32 n (by omega)
  unfold Iv at *
  show a + n ≤ (truncBits 32 (r32 x + i32 n)).toNat ∧ (truncBits 32 (r32 x + i32 n)).toNat ≤ b + n
  rw [toNat_tb_add, toNat_r32, hn, Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem iv_addi_neg (hx : Iv a b x) (n : Nat) (hn : n ≤ a) (h : b < 2 ^ 32) :
    Iv (a - n) (b - n) (addi x (-(n : Int))) := by
  unfold Iv at *
  have hi : (i32 (-(n : Int))).toNat = (2 ^ 32 - n) % 2 ^ 32 := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have h1 : (-(n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = 2 ^ 64 - n := by omega
      rw [h1]; omega
  show a - n ≤ (truncBits 32 (r32 x + i32 (-(n : Int)))).toNat ∧
    (truncBits 32 (r32 x + i32 (-(n : Int)))).toNat ≤ b - n
  rw [toNat_tb_add, toNat_r32, hi, Nat.mod_eq_of_lt (a := x.toNat) (by omega)]
  omega

theorem iv_sel {cnd : Bool} (h1 : Iv a b x) (h2 : Iv a b y) : Iv a b (sel cnd x y) := by
  unfold sel; split <;> assumption

theorem iv_andi (n : Nat) (h : n < 2 ^ 32) : Iv 0 n (andi x n) := by
  unfold Iv
  simp only [andi, BitVec.toNat_and, toNat_i32 n h]
  exact ⟨Nat.zero_le _, Nat.and_le_right⟩

theorem iv_or (hx : Iv a b x) (hy : Iv c d y) : Iv a (b + d) (x ||| y) := by
  unfold Iv at *
  have := nat_or_add_and x.toNat y.toNat
  simp only [BitVec.toNat_or]
  exact ⟨hx.1.trans Nat.left_le_or, by omega⟩

theorem toNat_tb_shl (u : BitVec 64) (k : Nat) :
    (truncBits 32 (u <<< k)).toNat = u.toNat * 2 ^ k % 2 ^ 64 % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem iv_shl (hx : Iv a b x) (k : Nat) (hk : k < 32) (h : b * 2 ^ k < 2 ^ 32) :
    Iv (a * 2 ^ k) (b * 2 ^ k) (shl x k) := by
  have hb : b < 2 ^ 32 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)) h
  have hik := toNat_i32 k (by omega)
  unfold Iv at *
  have he : shl x k = truncBits 32 (r32 x <<< k) := by
    show (if (i32 k).toNat ≥ 32 then 0 else truncBits 32 (r32 x <<< (i32 k).toNat)) = _
    simp only [hik, show ¬ k ≥ 32 by omega, ↓reduceIte]
  rw [he, toNat_tb_shl, toNat_r32, Nat.mod_eq_of_lt (a := x.toNat) (by omega)]
  have h1 : x.toNat * 2 ^ k ≤ b * 2 ^ k := Nat.mul_le_mul_right _ hx.2
  have h2 : a * 2 ^ k ≤ x.toNat * 2 ^ k := Nat.mul_le_mul_right _ hx.1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem iv_shru (hx : Iv a b x) (k : Nat) (hk : k < 32) (hb : b < 2 ^ 32) :
    Iv (a / 2 ^ k) (b / 2 ^ k) (shru x k) := by
  have hik := toNat_i32 k (by omega)
  unfold Iv at *
  have he : shru x k = r32 x >>> k := by
    show (if (i32 k).toNat ≥ 32 then 0 else r32 x >>> (i32 k).toNat) = _
    simp only [hik, show ¬ k ≥ 32 by omega, ↓reduceIte]
  have hs : (r32 x >>> k).toNat = (r32 x).toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [he, hs, toNat_r32, Nat.mod_eq_of_lt (a := x.toNat) (by omega)]
  exact ⟨Nat.div_le_div_right hx.1, Nat.div_le_div_right hx.2⟩

/-- **An exclusive or with a word at most `m` moves a word by at most `m`.** -/
theorem iv_xor32 {m : Nat} (hy : Iv 0 m y) (hx : Iv a b x) (hm : m < 2 ^ 32)
    (hb : b < 2 ^ 32) : Iv (a - m) (b + m) (xor32 y x) := by
  unfold Iv at *
  have := nat_xor_add_and y.toNat x.toNat
  have hand : y.toNat &&& x.toNat ≤ y.toNat := Nat.and_le_left
  simp only [xor32, BitVec.toNat_xor, toNat_r32]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega)]
  omega

/-- **The swizzle of a shared address moves it by at most 112.** -/
theorem iv_swz (hx : Iv a b x) (hb : b < 2 ^ 32) :
    Iv (a - 112) (b + 112) (xor32 (andi (shru x 3) 112) x) :=
  iv_xor32 (iv_andi 112 (by decide)) hx (by decide) hb

/-- `add32 x (sel c y z)` is the choice of the two sums. -/
theorem add32_sel {cnd : Bool} : add32 x (sel cnd y z) = sel cnd (add32 x y) (add32 x z) := by
  unfold sel; split <;> rfl

/-- The sum of a word and a negative immediate word. -/
theorem iv_add32_neg (hx : Iv a b x) (n : Nat) (hn : n ≤ a) (h : b < 2 ^ 32) :
    Iv (a - n) (b - n) (add32 x (i32 (-(n : Int)))) := by
  have hr : r32 (i32 (-(n : Int))) = i32 (-(n : Int)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_r32]
    simp only [i32, truncBits, BitVec.toNat_ofNat]
    omega
  show Iv _ _ (truncBits 32 (r32 x + r32 (i32 (-(n : Int)))))
  rw [hr]
  exact iv_addi_neg hx n hn h

/-- **A signed step**: the word plus or minus `n` (a choice of the immediates `n` and `-n`) lies in
`[lo, hi]` when the word lies `n` inside it. The backward form, for a closure that states the
interval of the result and asks the operand's. -/
theorem iv_pm {lo hi : Nat} {cnd : Bool} (n : Int) (hn : 0 ≤ n)
    (hx : Iv (lo + n.toNat) (hi - n.toNat) x) (hh : n.toNat ≤ hi) (h : hi < 2 ^ 32) :
    Iv lo hi (add32 x (sel cnd (i32 n) (i32 (-n)))) := by
  have e1 : n = ((n.toNat : Nat) : Int) := (Int.toNat_of_nonneg hn).symm
  rw [add32_sel]
  refine iv_sel ?_ ?_
  · have := iv_add32 hx (iv_i32 n.toNat (by omega)) (by omega)
    rw [← e1] at this
    exact iv_mono (by omega) (by omega) this
  · have := iv_add32_neg hx n.toNat (by omega) (by omega)
    rw [← e1] at this
    exact iv_mono (by omega) (by omega) this

/-- **A shared effective address that does not wrap** is the register's word plus the offset. -/
theorem eff_shared {off : Nat} (h : x.toNat + off < 2 ^ 32) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 (off : Int))).toNat = x.toNat + off := by
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have h1 : ((off : Int) % ((2 ^ 64 : Nat) : Int)).toNat = off := by omega
  rw [h1, Nat.mod_eq_of_lt (a := x.toNat) (by omega)]
  omega

/-- `eff_shared` for a nonnegative integer offset, as the instruction states it. -/
theorem eff_sharedI {off : Int} (h0 : 0 ≤ off) (h : x.toNat + off.toNat < 2 ^ 32) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat = x.toNat + off.toNat := by
  have e1 : off = ((off.toNat : Nat) : Int) := (Int.toNat_of_nonneg h0).symm
  rw [e1, eff_shared h, Int.toNat_natCast]

/-- **The bounds of a shared effective address** plus an element offset, from the interval of
the register's word. -/
theorem eff_le {lo hi A B s : Nat} {off : Int} (hx : Iv lo hi x) (h0 : 0 ≤ off)
    (hh : hi + off.toNat < 2 ^ 32) (hlo : A ≤ lo) (hhi : hi + off.toNat + s ≤ B) :
    A ≤ (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat + s ∧
      (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat + s ≤ B := by
  unfold Iv at hx
  rw [eff_sharedI h0 (by omega)]
  omega

end PTX.Flow.Arith32
