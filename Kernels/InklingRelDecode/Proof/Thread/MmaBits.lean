-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Bits
public import Lemmas.Flow.BitForms

@[expose] public section

/-! # Bit arithmetic of the MMA warp's loop

The loop of the MMA warp computes the ring slot and parity of an iteration with a multiply-high
by `0xAAAAAAAB` and a shift (`i / 3`), and the start address field of a descriptor with a bit
field extract (`bfe.u32 d, a, 4, 15`). These are the integer forms of those operations, in the
normal form `norm_bits` produces. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

theorem bitsFrom_add_aux (f : Nat → Bool) (l : List Nat) (a : Nat) :
    l.foldr (fun j acc => if f j then acc + 2 ^ j else acc) a =
      a + l.foldr (fun j acc => if f j then acc + 2 ^ j else acc) 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    split <;> omega

theorem bitsFrom_succ (w : Nat) (f : Nat → Bool) :
    bitsFrom (w + 1) f = bitsFrom w f + (if f w then 2 ^ w else 0) := by
  unfold bitsFrom
  rw [List.range_succ, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [bitsFrom_add_aux]
  split <;> omega

theorem bitsFrom_lt (w : Nat) (f : Nat → Bool) : bitsFrom w f < 2 ^ w := by
  induction w with
  | zero => simp [bitsFrom]
  | succ w ih =>
    rw [bitsFrom_succ, Nat.pow_succ]
    split <;> omega

theorem bitsFrom_testBit (w : Nat) (f : Nat → Bool) (j : Nat) :
    (bitsFrom w f).testBit j = (decide (j < w) && f j) := by
  induction w with
  | zero => simp [bitsFrom]
  | succ w ih =>
    rw [bitsFrom_succ]
    have hlt := bitsFrom_lt w f
    by_cases hf : f w
    · simp only [hf, ↓reduceIte]
      rw [Nat.add_comm]
      rcases Nat.lt_trichotomy j w with hj | hj | hj
      · rw [Nat.testBit_two_pow_add_gt hj, ih]
        simp [hj, show j < w + 1 by omega]
      · subst hj
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        simp [hf]
      · have h2 : 2 ^ w + bitsFrom w f < 2 ^ j := by
          have : 2 ^ (w + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          rw [Nat.pow_succ] at this
          omega
        rw [Nat.testBit_lt_two_pow h2]
        simp [show ¬ j < w + 1 by omega]
    · simp only [hf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [ih]
      rcases Nat.lt_trichotomy j w with hj | hj | hj
      · simp [hj, show j < w + 1 by omega]
      · subst hj; simp [hf]
      · simp [show ¬ j < w by omega, show ¬ j < w + 1 by omega]

/-- `bfe.u32 d, a, pos, len`: the `len` bits of the operand from bit `pos`, when they are
within the 32 bits. -/
theorem bfe_u32 (x pos len : Nat) (h : pos + len ≤ 32) :
    bfeBits .u 32 x pos len = x % 2 ^ 32 / 2 ^ pos % 2 ^ len := by
  apply Nat.eq_of_testBit_eq
  intro j
  unfold bfeBits
  simp only [bitsFrom_testBit]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  rw [Nat.add_comm j pos]
  by_cases h1 : j < len
  · have h4 : j < 32 := by omega
    have h5 : pos + j ≤ 31 := by omega
    have h6 : pos + j < 32 := by omega
    simp [h1, h4, h5, h6]
  · simp [h1]

/-- `or.b64` of a start address field (below `2 ^ 15`) with a constant whose low 26 bits are
zero (a descriptor's fixed high part): their sum. -/
theorem lor_field (y C : Nat) (hC : C % 67108864 = 0) :
    y % 32768 % 4294967296 ||| C = y % 32768 + C := by
  have hx : y % 32768 < 2 ^ 26 := by omega
  have hx' : y % 32768 % 4294967296 = y % 32768 := Nat.mod_eq_of_lt (by omega)
  have hk : C = 2 ^ 26 * (C / 2 ^ 26) := by omega
  rw [hx', Nat.or_comm, hk, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

/-- `0xAAAAAAAB = ⌈2 ^ 33 / 3⌉`: the multiply-high quotient. -/
theorem mulhi_core (y q : Nat) (hy : y < 4294967296) (hq1 : 4294967296 * q ≤ y * 2863311531)
    (hq2 : y * 2863311531 < 4294967296 * (q + 1)) : q / 2 = y / 3 := by
  omega

/-- `mul.hi.u32 t, i, 0xAAAAAAAB` followed by `shr.u32 d, t, 1` is `i / 3`, in the normal
form of `norm_bits`. -/
theorem mulhi3 (x : Nat) :
    ((↑(x % 4294967296) : Int) * ((2863311531 : Nat) : Int) / 2 ^ 32 % 18446744073709551616).toNat %
      4294967296 / 2 % 18446744073709551616 = x % 4294967296 / 3 := by
  have hx : x % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  obtain ⟨y, hy⟩ : ∃ y, y = x % 4294967296 := ⟨_, rfl⟩
  rw [← hy] at hx ⊢
  obtain ⟨q, hq⟩ : ∃ q : Nat, (q : Int) = (y : Int) * ((2863311531 : Nat) : Int) / 2 ^ 32 :=
    ⟨((y : Int) * ((2863311531 : Nat) : Int) / 2 ^ 32).toNat, by omega⟩
  rw [← hq]
  have hq1 : 4294967296 * q ≤ y * 2863311531 := by omega
  have hq2 : y * 2863311531 < 4294967296 * (q + 1) := by omega
  have := mulhi_core y q hx hq1 hq2
  have hq3 : q < 4294967296 := by omega
  have : (((q : Int) % 18446744073709551616).toNat) = q := by omega
  rw [this, Nat.mod_eq_of_lt hq3, Nat.mod_eq_of_lt (by omega)]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Mma
