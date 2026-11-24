-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-! # 32-bit address words

A shared address is `mov.b32` of the shared base followed by `add.s32` of a constant offset;
the addition truncates to 32 bits. When the exact sum fits in 32 bits, the truncated chain is
the sum. -/

namespace PTX

/-- `truncBits 32 (truncBits 32 x + truncBits 32 c) = ofNat (x + c)` when `x + c < 2 ^ 32`
and `c` is the non-negative constant. -/
theorem trunc32_add {x c : Nat} (hc : 0 ≤ c) (h : x + c < 2 ^ 32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) + truncBits 32 (BitVec.ofInt 64 c)) =
      BitVec.ofNat 64 (x + c) := by
  have hx : x < 2 ^ 64 := by omega
  have hc64 : c < 2 ^ 64 := by omega
  have hx32 : x < 2 ^ 32 := by omega
  have hc32 : c < 2 ^ 32 := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.ofInt_natCast, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    Nat.mod_eq_of_lt hx32, Nat.mod_eq_of_lt hc32, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hc64]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The same for a base that already is a 32-bit word. -/
theorem trunc32_add_of_word {x c : Nat} (hx : x < 2 ^ 32) (hc : 0 ≤ c) (h : x + c < 2 ^ 32) :
    truncBits 32 ((BitVec.ofNat 64 x) + truncBits 32 (BitVec.ofInt 64 c)) =
      BitVec.ofNat 64 (x + c) := by
  have h1 : truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat]
    omega
  rw [← h1]
  exact trunc32_add hc h

end PTX
