-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Bits
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # `or` and `xor` of operands with disjoint bits

A proof tool for the normal form of `Lemmas/Flow/Bits.lean`, whose rules leave `|||` and
`^^^` of two `Nat` expressions in place. Address arithmetic combines a multiple of `2^k` with
a value below `2^k` (a field of a packed address, the 128-byte swizzle's XOR of the row's low
bits into the 16-byte chunk index): then `or` and `xor` are sums (`lor_eq_add`,
`xor_eq_add`). `xor` of the normal form's `BitVec` values is a `Nat` `xor` (`nf_xor`), and
`xor` with `1` flips a parity (`xor_one_mod2`). A swizzled 16-byte chunk index `x % 8 ^^^ c`
is a sum over its three bits (`xor_mod8`). -/

namespace PTX.Proof
open PTX

theorem nf_xor (a b : Nat) : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 ^^^ b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos 64))
    (Nat.mod_lt _ (Nat.two_pow_pos 64)))).symm

/-- `or` of a multiple of `2^k` and a value below `2^k` is their sum. -/
theorem lor_eq_add {x y : Nat} (k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) :
    x ||| y = x + y := by
  have e : x = 2 ^ k * (x / 2 ^ k) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)).symm
  rw [e, ← Nat.two_pow_add_eq_or_of_lt hy]

/-- `xor` of a multiple of `2^k` and a value below `2^k` is their sum. -/
theorem xor_eq_add {x y : Nat} (k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) :
    x ^^^ y = x + y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, ← lor_eq_add k hx hy, Nat.testBit_or]
  by_cases hi : i < k
  · have h := Nat.testBit_mod_two_pow x k i
    rw [hx, Nat.zero_testBit] at h
    simp only [hi, decide_true, Bool.true_and] at h
    simp [← h]
  · have : y.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

/-- `xor` with `1` of a parity flips it. -/
theorem xor_one_mod2 (x : Nat) : x % 2 ^^^ 1 = (x + 1) % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega

/-- `xor` of a three-bit index with `c < 8`, bit by bit. -/
theorem xor_mod8 (x : Nat) {c : Nat} (hc : c < 8) : x % 8 ^^^ c =
    (x % 2 ^^^ c % 2) + 2 * (x / 2 % 2 ^^^ c / 2 % 2) + 4 * (x / 4 % 2 ^^^ c / 4 % 2) := by
  have e1 : x % 2 = x % 8 % 2 := by omega
  have e2 : x / 2 % 2 = x % 8 / 2 % 2 := by omega
  have e4 : x / 4 % 2 = x % 8 / 4 % 2 := by omega
  rw [e1, e2, e4]
  have hy : x % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize x % 8 = y at hy ⊢
  interval_cases y <;> interval_cases c <;> rfl

/-- Setting bit `k` of a three-bit chunk index `c` (clear there) moves `x ^^^ c` by `2^k`, up
when bit `k` of `x` is clear, down when it is set. -/
theorem xor_flip {x c k : Nat} (hx : x < 8) (hc : c < 8) (hk : k < 3) (hb : c / 2 ^ k % 2 = 0) :
    (x / 2 ^ k % 2 = 0 → (x ^^^ c) + 2 ^ k = x ^^^ (c + 2 ^ k)) ∧
      (x / 2 ^ k % 2 = 1 → (x ^^^ c) = (x ^^^ (c + 2 ^ k)) + 2 ^ k) := by
  revert hb
  interval_cases x <;> interval_cases c <;> interval_cases k <;> decide

end PTX.Proof
