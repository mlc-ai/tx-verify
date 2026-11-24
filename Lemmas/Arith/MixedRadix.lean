-- SPDX-License-Identifier: Apache-2.0
module

@[expose] public section

/-! # Two digits in a base

A proof tool for index arithmetic: a number `a · n + b` with `b < n` determines its two digits
(`Nat.digits_of_eq`), which are its quotient and remainder (`Nat.digits_of_lt`). -/

namespace PTX

/-- **The two digits of a number in base `n` are unique.** -/
theorem Nat.digits_of_eq {a b c d n : Nat} (hb : b < n) (hd : d < n)
    (h : a * n + b = c * n + d) : a = c ∧ b = d := by
  have hn : 0 < n := by omega
  have e1 : (b + a * n) / n = a := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  have e2 : (d + c * n) / n = c := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hd, Nat.zero_add]
  have e3 : (b + a * n) % n = b := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have e4 : (d + c * n) % n = d := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  have h' : b + a * n = d + c * n := by omega
  rw [h'] at e1 e3
  exact ⟨e1.symm.trans e2, e3.symm.trans e4⟩

/-- The quotient and remainder of `q · n + m` by `n`, for `m < n`. -/
theorem Nat.digits_of_lt {q m n : Nat} (hm : m < n) :
    (q * n + m) / n = q ∧ (q * n + m) % n = m := by
  have hn : 0 < n := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hm, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  exact ⟨rfl, rfl⟩

end PTX
