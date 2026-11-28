-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.WideBits
import Lemmas.Flow.SignedBits

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Proof PTX.Flow

export Lib (toSigned32_ofNat toSigned64_ofNat sx_two ofInt_two madwide_s32 sx_small sx_big)

theorem cmp_lt_s64_neg (a c : Nat) (ha : a < 2 ^ 63) (hc1 : 2 ^ 63 ≤ c) (hc2 : c < 2 ^ 64) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 c)) = false := by
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc2
  simp only [PTX.compare, toSigned64_ofNat, h1, h2]
  have e1 : a < 2 ^ 63 := ha
  have e2 : ¬ c < 2 ^ 63 := by omega
  simp only [e1, e2, ↓reduceIte, decide_eq_false_iff_not]
  omega

theorem cmp_lt_s64_pos (a c : Nat) (ha : a < 2 ^ 63) (hc : c < 2 ^ 63) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 c)) = decide (a < c) := by
  have h1 : a % 2 ^ 64 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  simp only [PTX.compare, toSigned64_ofNat, h1, h2, ha, hc, ↓reduceIte, decide_eq_decide]
  omega

/-- Signed 32-bit `>=` of two words below `2 ^ 31`. -/
theorem cmp_ge_s32 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    PTX.compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = decide (b ≤ a) := by
  simp only [PTX.compare, toSigned32_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 32 by omega), ha, hb, ↓reduceIte, ge_iff_le, decide_eq_decide]
  omega

/-- Signed 64-bit `<` of a counter below `2 ^ 63` and the sign extension of a word. -/
theorem cmp_lt_s64 (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 32) :
    PTX.compare .lt .s 64 (truncBits 64 (BitVec.ofNat 64 a))
      (truncBits 64 (BitVec.ofNat 64 (sx b))) = decide (a < b ∧ b < 2 ^ 31) := by
  by_cases hb31 : b < 2 ^ 31
  · rw [sx_small hb31, cmp_lt_s64_pos a b ha (by omega), decide_eq_decide]
    omega
  · have h : 2 ^ 63 ≤ sx b := by rw [sx_big (by omega) hb]; omega
    have h' : sx b < 2 ^ 64 := by rw [sx_big (by omega) hb]; omega
    rw [cmp_lt_s64_neg a _ ha h h', Bool.false_eq, decide_eq_false_iff_not]
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
