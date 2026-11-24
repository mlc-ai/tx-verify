-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProADefs

@[expose] public section

/-! # The code's 32-bit integer operations on numbers

Each theorem gives the value of one of the integer operations of `ProADefs` (`wAdd32` …) on
operands `BitVec.ofNat 64 a`, as `BitVec.ofNat 64 e` for a `Nat` expression `e` of the operands.
The register table is built from these operations only, so a register that is a composition of
them is a closed `Nat` expression, proved one operation at a time over `Nat` arithmetic
(`omega`, `Nat.div` facts), without unfolding the evaluator's terms. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section

theorem pw_two_pow (n : Nat) : pw n = (2 : Int) ^ n := by
  simp [pw]

theorem truncBits_ofNat (w a : Nat) (hw : w ≤ 64) :
    truncBits w (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a % 2 ^ w) := by
  have : 2 ^ w ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hw
  simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ this]

theorem tos32 (n : Nat) : toSigned 32 (BitVec.ofNat 64 n) =
    if n % 2 ^ 32 < 2 ^ 31 then ((n % 2 ^ 32 : Nat) : Int)
    else ((n % 2 ^ 32 : Nat) : Int) - 2 ^ 32 := by
  have h : n % 2 ^ 64 % 2 ^ 32 = n % 2 ^ 32 := Nat.mod_mod_of_dvd n (by decide)
  simp only [toSigned, BitVec.toNat_ofNat, h]

theorem cmpMax : (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
    = Cmp.gt := by decide
theorem cmpMin : (if (IntOp.min false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
    = Cmp.lt := by decide
theorem tyS : (if (some IType.s == some IType.s) = true then IType.s else IType.u) = IType.s := by
  decide
theorem tyU : (if (some IType.u == some IType.s) = true then IType.s else IType.u) = IType.u := by
  decide

theorem wMaxS32_eq (a b : BitVec 64) : wMaxS32 a b =
    if toSigned 32 (truncBits 32 b) < toSigned 32 (truncBits 32 a) then truncBits 32 a
    else truncBits 32 b := by
  unfold wMaxS32
  rw [cmpMax, tyS]
  simp [PTX.compare]

theorem wMinS32_eq (a b : BitVec 64) : wMinS32 a b =
    if toSigned 32 (truncBits 32 a) < toSigned 32 (truncBits 32 b) then truncBits 32 a
    else truncBits 32 b := by
  unfold wMinS32
  rw [cmpMin, tyS]
  simp [PTX.compare]

theorem wMinU32_eq (a b : BitVec 64) : wMinU32 a b =
    if (truncBits 32 a).toNat < (truncBits 32 b).toNat then truncBits 32 a
    else truncBits 32 b := by
  unfold wMinU32
  rw [cmpMin, tyU]
  simp [PTX.compare]


/-- `max.s32` of two words below `2 ^ 31`. -/
theorem wMaxS32_pos (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    wMaxS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (max a b) := by
  simp only [wMaxS32_eq, truncBits_ofNat _ _ (by omega : 32 ≤ 64), tos32]
  have e1 : a % 2 ^ 32 % 2 ^ 32 = a := by omega
  have e2 : b % 2 ^ 32 % 2 ^ 32 = b := by omega
  simp only [e1, e2, ha, hb, ↓reduceIte]
  split_ifs <;> (refine congrArg (BitVec.ofNat 64) ?_; omega)

/-- `min.s32` of two words below `2 ^ 31`. -/
theorem wMinS32_pos (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    wMinS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (min a b) := by
  simp only [wMinS32_eq, truncBits_ofNat _ _ (by omega : 32 ≤ 64), tos32]
  have e1 : a % 2 ^ 32 % 2 ^ 32 = a := by omega
  have e2 : b % 2 ^ 32 % 2 ^ 32 = b := by omega
  simp only [e1, e2, ha, hb, ↓reduceIte]
  split_ifs <;> (refine congrArg (BitVec.ofNat 64) ?_; omega)

/-- `min.u32` of two words. -/
theorem wMinU32_ofNat (a b : Nat) :
    wMinU32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (min (a % 2 ^ 32) (b % 2 ^ 32)) := by
  simp only [wMinU32_eq, truncBits_ofNat _ _ (by omega : 32 ≤ 64), BitVec.toNat_ofNat]
  have e1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := by omega
  have e2 : b % 2 ^ 32 % 2 ^ 64 = b % 2 ^ 32 := by omega
  rw [e1, e2]
  split_ifs <;> (refine congrArg (BitVec.ofNat 64) ?_; omega)

theorem wAdd32_ofNat (a b : Nat) :
    wAdd32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 ((a + b) % 2 ^ 32) := by
  simp only [wAdd32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem wSub32_ofNat (a b : Nat) :
    wSub32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 ((a % 2 ^ 32 + (2 ^ 32 - b % 2 ^ 32)) % 2 ^ 32) := by
  simp only [wSub32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem wShrU32_ofNat (a k : Nat) (hk : k < 32) :
    wShrU32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 k) = BitVec.ofNat 64 (a % 2 ^ 32 / 2 ^ k) := by
  simp only [wShrU32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  have h1 : (BitVec.ofNat 64 (k % 2 ^ 32)).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  rw [h1]
  split_ifs with hh
  · omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h2 : a % 2 ^ 32 < 2 ^ 64 := by omega
  have h3 : a % 2 ^ 32 / 2 ^ k < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) h2
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]

theorem wShrS32_ofNat (a k : Nat) (ha : a < 2 ^ 31) (hk : k ≤ 32) :
    wShrS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 k) = BitVec.ofNat 64 (a / 2 ^ k) := by
  simp only [wShrS32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  have h1 : (BitVec.ofNat 64 (k % 2 ^ 32)).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  have h2 : a % 2 ^ 32 = a := Nat.mod_eq_of_lt (by omega)
  rw [h1, tos32, Nat.min_eq_left hk, pw_two_pow]
  split_ifs with hh
  · have e : ((a % 2 ^ 32 % 2 ^ 32 : Nat) : Int) = (a : Int) := by omega
    rw [e, show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by norm_cast, ← Int.natCast_ediv,
      BitVec.ofInt_natCast, truncBits_ofNat _ _ (by omega)]
    congr 1
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  · omega

theorem wAnd32_ofNat (a b : Nat) :
    wAnd32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 ((a % 2 ^ 32) &&& (b % 2 ^ 32)) := by
  simp only [wAnd32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have h2 : b % 2 ^ 32 % 2 ^ 64 = b % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  have h3 : (a % 2 ^ 32) &&& (b % 2 ^ 32) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.and_le_left) (by omega)
  rw [h1, h2, Nat.mod_eq_of_lt h3]

theorem wNot32_ofNat (a : Nat) :
    wNot32 (BitVec.ofNat 64 a) = BitVec.ofNat 64 (2 ^ 32 - 1 - a % 2 ^ 32) := by
  simp only [wNot32, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_not, BitVec.toNat_ofNat]
  omega

theorem wDivS32_ofNat (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    wDivS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / b) := by
  simp only [wDivS32, intOf, truncBits_ofNat 32 _ (by omega : 32 ≤ 64), tos32]
  have e1 : a % 2 ^ 32 % 2 ^ 32 = a := by omega
  have e2 : b % 2 ^ 32 % 2 ^ 32 = b := by omega
  simp only [e1, e2, ha, hb, ↓reduceIte]
  have e3 : (↑a : Int).tdiv (↑b : Int) = ((a / b : Nat) : Int) := rfl
  have e4 : a / b < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) ha
  simp only [e3, intBits, BitVec.ofInt_natCast, truncBits_ofNat 32 _ (by omega : 32 ≤ 64)]
  rw [Nat.mod_eq_of_lt (by omega : a / b < 2 ^ 32)]

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
