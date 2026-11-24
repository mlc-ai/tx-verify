-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Local

@[expose] public section

/-! # Packing a 32-bit pattern with itself

A proof tool. Packing a 32-bit pattern with no bit above bit 31 with itself and splitting the
64-bit result returns the pattern twice (`split_join_bits`). -/

namespace PTX.Flow
open PTX

/-- **A 32-bit pattern packed with itself splits back into two copies.** -/
theorem split_join_bits {b : BitVec 64} (hb : b.toNat < 2 ^ 32) :
    splitValue 64 (joinValue (.bits 32 b) (.bits 32 b)) = (.bits 32 b, .bits 32 b) := by
  have hs : (b <<< 32).toNat = b.toNat * 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hx : (b ||| b <<< 32).toNat = b.toNat * 2 ^ 32 + b.toNat := by
    rw [BitVec.toNat_or, hs, Nat.or_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt hb]
  have hd : (b.toNat * 2 ^ 32 + b.toNat) / 2 ^ 32 = b.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]
  have hm : (b.toNat * 2 ^ 32 + b.toNat) % 2 ^ 32 = b.toNat := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  simp only [joinValue, splitValue, truncBits, and_self, Nat.reduceMul, Nat.reduceLeDiff,
    ↓reduceIte, Nat.reduceDiv, hx, hd, hm, Prod.mk.injEq, Value.bits.injEq]
  constructor <;> refine ⟨trivial, BitVec.eq_of_toNat_eq ?_⟩ <;> simp only [BitVec.toNat_ofNat] <;>
    omega

end PTX.Flow
