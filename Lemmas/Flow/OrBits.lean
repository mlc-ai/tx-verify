-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Arith.CeilDiv

@[expose] public section

/-! # `or` of disjoint bit fields

A proof tool for addresses built with `or.b32` of fields that occupy disjoint bits (a Tensor
Memory address: lane field `<< 16`, column offset): `x ||| y = x + y` when `x` is a multiple
of `2 ^ k` and `y < 2 ^ k` (`lor_eq_add`), and a field extracted by `and` with the mask of bits
`k … n-1` (`land_field`). -/

namespace PTX.Proof

theorem lor_eq_add {x y k : Nat} (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) : x ||| y = x + y := by
  have e : x = 2 ^ k * (x / 2 ^ k) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)).symm
  rw [e, ← Nat.two_pow_add_eq_or_of_lt hy]

/-- The bits `k … n-1` of `a`, by the mask `2 ^ n - 2 ^ k`. -/
theorem land_field (a n k : Nat) (hk : k ≤ n) :
    a &&& (2 ^ n - 2 ^ k) = a % 2 ^ n / 2 ^ k * 2 ^ k :=
  CeilDiv.land_highMask a n k hk

end PTX.Proof
