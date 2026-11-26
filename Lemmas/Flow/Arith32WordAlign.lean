-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32

@[expose] public section

/-! # Alignment of the code's 32-bit words (library candidate)

`Al k x`: the word `x` is a multiple of `2 ^ k`. For `k ≤ 32` the code's 32-bit operations keep
it: a sum, a bitwise and, or or exclusive or of aligned words, a left shift by at least `k`, an
`and` with an aligned immediate, a choice between aligned words. Addresses built by these
operations (a swizzled shared address plus signed lane offsets, for example) are aligned whether
or not their 32-bit sums wrap, which is all a store's alignment condition reads. `al_tac` closes
`Al k x` by these rules down to the leaves, which it leaves to `decide` or to hypotheses. -/

namespace PTX.Flow.Arith32
open PTX

/-- The word `x` is a multiple of `2 ^ k`. -/
def Al (k : Nat) (x : BitVec 64) : Prop := x.toNat % 2 ^ k = 0

variable {k : Nat}

theorem al_pow_dvd (hk : k ≤ 32) : 2 ^ k ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hk

theorem al_mod (hk : k ≤ 32) (a : Nat) : a % 2 ^ 32 % 2 ^ k = a % 2 ^ k :=
  Nat.mod_mod_of_dvd _ (al_pow_dvd hk)

theorem al_mod64 (hk : k ≤ 32) (a : Nat) : a % 2 ^ 64 % 2 ^ k = a % 2 ^ k :=
  Nat.mod_mod_of_dvd _ ((al_pow_dvd hk).trans (by decide))

theorem al_r32 (hk : k ≤ 32) {x : BitVec 64} (h : Al k x) : Al k (r32 x) := by
  unfold Al at *
  simp only [r32, truncBits, BitVec.toNat_ofNat, al_mod hk, al_mod64 hk]
  exact h

theorem al_add32 (hk : k ≤ 32) {x y : BitVec 64} (hx : Al k x) (hy : Al k y) :
    Al k (add32 x y) := by
  have h1 := al_r32 hk hx
  have h2 := al_r32 hk hy
  unfold Al at *
  simp only [add32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, al_mod hk,
    al_mod64 hk] at h1 h2 ⊢
  rw [Nat.add_mod]
  simp only [al_mod hk, al_mod64 hk, h1, h2, Nat.zero_add, Nat.zero_mod]

theorem al_addi (hk : k ≤ 32) {x : BitVec 64} {n : Int} (hx : Al k x) (hn : Al k (i32 n)) :
    Al k (addi x n) := by
  have h1 := al_r32 hk hx
  unfold Al at *
  simp only [addi, i32, r32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, al_mod hk,
    al_mod64 hk] at h1 hn ⊢
  rw [Nat.add_mod]
  simp only [al_mod hk, al_mod64 hk, h1, hn, Nat.zero_add, Nat.zero_mod]

theorem al_xor32 (hk : k ≤ 32) {x y : BitVec 64} (hx : Al k x) (hy : Al k y) :
    Al k (xor32 x y) := by
  have h1 := al_r32 hk hx
  have h2 := al_r32 hk hy
  unfold Al at *
  simp only [xor32, BitVec.toNat_xor, Nat.xor_mod_two_pow, h1, h2, Nat.zero_xor]

theorem al_or {x y : BitVec 64} (hx : Al k x) (hy : Al k y) : Al k (x ||| y) := by
  unfold Al at *
  simp only [BitVec.toNat_or, Nat.or_mod_two_pow, hx, hy, Nat.zero_or]

theorem al_and_right {x y : BitVec 64} (hy : Al k y) : Al k (x &&& y) := by
  unfold Al at *
  simp only [BitVec.toNat_and, Nat.and_mod_two_pow, hy, Nat.and_zero]

theorem al_andi {x : BitVec 64} {n : Int} (hn : Al k (i32 n)) : Al k (andi x n) :=
  al_and_right hn

theorem al_sel {c : Bool} {x y : BitVec 64} (hx : Al k x) (hy : Al k y) : Al k (sel c x y) := by
  unfold sel; split <;> assumption

theorem al_shl (hk : k ≤ 32) {x : BitVec 64} {n : Int} (hn : k ≤ (i32 n).toNat) :
    Al k (shl x n) := by
  unfold Al shl
  split
  · simp
  · simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, al_mod hk, al_mod64 hk,
      Nat.shiftLeft_eq]
    exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hn) _)

/-- One rule of `al_tac`. -/
macro "al_step" : tactic => `(tactic| first
  | with_reducible assumption
  | (with_reducible apply al_add32 (by decide))
  | (with_reducible apply al_addi (by decide))
  | (with_reducible apply al_xor32 (by decide))
  | (with_reducible apply al_sel)
  | (with_reducible apply al_or)
  | (with_reducible apply al_andi; unfold Al; decide)
  | (with_reducible apply al_shl (by decide) (by decide))
  | (with_reducible apply al_r32 (by decide))
  | (unfold Al; decide))

/-- Close `Al k x` by the rules above; leaves are left to `decide` and the context. -/
macro "al_tac" : tactic => `(tactic| repeat al_step)

end PTX.Flow.Arith32
