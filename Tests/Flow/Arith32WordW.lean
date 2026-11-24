-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32WordWide

/-! # The 32-bit arithmetic of words: masks, signed max/min, negation and subtraction

FlashMLA request G17, checked on literal words: the signed maximum of two small words is the
maximum of the numbers, the mask `-(2 ^ k)` rounds a word down to a multiple of `2 ^ k`, the
wrapping negation and subtraction are the differences modulo `2 ^ 32`, and a ring slot's update
`(s + 1) - ((s + 1) & -4)` is `(s + 1) % 4`. -/

namespace PTX.Tests.Arith32WordW
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

/-- The signed maximum of two words is the maximum of their numbers. -/
example : max32 (W 3) (W 7) = W 7 := by
  rw [max32_W (by decide) (by decide)]
  rfl

example (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    max32 (W a) (W b) = W (max a b) := max32_W ha hb

/-- The mask `-(2 ^ k)` rounds a word down: `13 & -4 = 12`, `-8` clears three bits. -/
example : andi (W 13) (-(2 ^ 2 : Nat) : Int) = W 12 := by
  rw [andi_W_negpow (by decide) (by decide)]
  rfl

example : andi (W 13) (-(2 ^ 3 : Nat) : Int) = W 8 := by
  rw [andi_W_negpow (by decide) (by decide)]
  rfl

/-- The wrapping negation and subtraction are the differences modulo `2 ^ 32`. -/
example : neg32 (W 1) = W (2 ^ 32 - 1) := by
  rw [neg32_W (by decide)]
  rfl

example : sub32 (W 1) (W 2) = W (2 ^ 32 - 1) := by
  rw [sub32_W_mod (by decide) (by decide)]
  rfl

example : sub32 (W 9) (W 4) = W 5 := by
  rw [sub32_W_mod (by decide) (by decide)]
  rfl

/-- A ring slot's update: `(3:ℕ) - (3 & -4)` is `3 % 4`, and a full ring wraps at four. -/
example : sub32 (W 3) (andi (W 3) (-(2 ^ 2 : Nat) : Int)) = W (3 % 4) :=
  slot_update_W (by decide)

example : sub32 (W 3) (andi (W 3) (-(2 ^ 2 : Nat) : Int)) = W 3 := by
  rw [slot_update_W (by decide)]

example : sub32 (W 4) (andi (W 4) (-(2 ^ 2 : Nat) : Int)) = W 0 := by
  rw [slot_update_W (by decide)]

/-- The slot update with the increment folded in: the ring slot `(s + 1) % 4` from `s + 1`. -/
example (s : Nat) (hs : s < 2 ^ 31) :
    sub32 (W (s + 1)) (andi (W (s + 1)) (-(2 ^ 2 : Nat) : Int)) = W ((s + 1) % 4) :=
  slot_update_W (by omega)

end PTX.Tests.Arith32WordW
