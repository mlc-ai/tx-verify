-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LoaderBase

@[expose] public section

/-! # What the loader's ring registers mean

The table states the registers that depend on the ring slot as the code's own terms (`quotW`,
`slotW`, `barW`, …). For a counter `i` below `2 ^ 31` they are the exact values the source
computes: `%r138 = i / 3`, the slot offset `%r140 = 8 (i % 3)` and `%r144 = 32768 (i % 3)`, the
`kv_empty` barrier of slot `i % 3` at `212992 + 256 + ...` bytes above the shared base (the
barrier address plus the offset), and the parity `1 - (i / 3) % 2`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- `%r138`: `mul.hi.s32` by `1431655766` and the correction by its sign bit compute `i / 3`. -/
theorem quotW_eq {i : Nat} (hi : i < 2 ^ 31) : quotW i = BitVec.ofNat 64 (i / 3) := by
  have h3 := mulhi3 i hi
  unfold quotW addW mulHiW shrW
  simp only [pow32]
  nf_simp [toSigned]
  split_ifs <;> omega

/-- `%r140`: the slot's offset in the barrier arrays, `8 (i % 3)`. -/
theorem slotW_eq {i : Nat} (hi : i < 2 ^ 31) : slotW i = BitVec.ofNat 64 (8 * (i % 3)) := by
  unfold slotW madLoW
  rw [quotW_eq hi]
  nf_simp
  omega

/-- `%r144`: the slot's offset in the tile ring, `32768 (i % 3)`. -/
theorem slotKW_eq {i : Nat} (hi : i < 2 ^ 31) :
    slotKW i = BitVec.ofNat 64 (32768 * (i % 3)) := by
  unfold slotKW madLoW
  rw [quotW_eq hi]
  nf_simp
  omega

theorem not32_eq (a : Nat) :
    truncBits 32 (~~~BitVec.ofNat 64 a) = BitVec.ofNat 64 (4294967295 - a % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_not]
  omega

/-- The parity of the `kv_empty` poll: `1 - (i / 3) % 2`. -/
theorem parity_eq {i : Nat} (hi : i < 2 ^ 31) :
    andW (notW (quotW i)) (BitVec.ofInt 64 1) = BitVec.ofNat 64 (1 - i / 3 % 2) := by
  rw [quotW_eq hi]
  unfold andW notW
  nf_simp [not32_eq, Nat.and_one_is_mod]
  omega

/-! ### Every 32-bit counter

For a counter `i ≥ 2 ^ 31` (negative as `s32`) the code's quotient is rounded toward zero, so the
slot remainder `remI i` is in `-2 … 2` and the offsets are `32768 · remI i` and `8 · remI i` modulo
`2 ^ 32` (`slotKW_toNat`, `slotW_toNat`); below `2 ^ 31` they are the ones above. The signed
counter `sxI`, its quotient `quoI` and the remainder `remI` are defined with the machine
(`Loader.lean`). -/

theorem sign_fix (M : Int) (h1 : -2 ^ 31 ≤ M) (h2 : M < 2 ^ 31) :
    ((((M % 18446744073709551616).toNat % 4294967296 +
      (M % 18446744073709551616).toNat % 4294967296 / 2147483648 % 4294967296) % 4294967296 :
        Nat) : Int) = (if M < 0 then M + 1 else M) % 4294967296 := by
  have h0 : 0 ≤ M % 18446744073709551616 := Int.emod_nonneg _ (by norm_num)
  have h3 : ((M % 18446744073709551616).toNat : Int) = M % 18446744073709551616 :=
    Int.toNat_of_nonneg h0
  generalize (M % 18446744073709551616).toNat = T at h3 ⊢
  push_cast
  split_ifs <;> omega

/-- `mul.hi.s32` by `1431655766` of a nonnegative word is its third, rounded down. -/
theorem mulhi_pos (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 31) :
    x * 1431655766 / 4294967296 = x / 3 :=
  ((Int.ediv_emod_unique (a := x * 1431655766) (b := 4294967296)
    (r := x * 1431655766 - 4294967296 * (x / 3)) (q := x / 3) (by norm_num)).mpr
    ⟨by ring, by omega, by omega⟩).1

/-- `mul.hi.s32` by `1431655766` of a negative word is its third rounded toward zero, minus one;
the sign bit the code adds makes up the difference. -/
theorem mulhi_neg (x : Int) (h0 : -2 ^ 31 ≤ x) (h1 : x < 0) :
    x * 1431655766 / 4294967296 = -((-x) / 3) - 1 :=
  ((Int.ediv_emod_unique (a := x * 1431655766) (b := 4294967296)
    (r := x * 1431655766 - 4294967296 * (-((-x) / 3) - 1)) (q := -((-x) / 3) - 1)
    (by norm_num)).mpr ⟨by ring, by omega, by omega⟩).1

/-- `%r138` for every counter: the signed third rounded toward zero, as a 32-bit word. -/
theorem quotW_toNat (i : Nat) : ((quotW i).toNat : Int) = quoI i % 2 ^ 32 := by
  unfold quotW addW mulHiW shrW
  simp only [pow32]
  nf_simp [toSigned]
  unfold quoI sxI
  simp only [Nat.cast_ofNat, Int.reducePow, Nat.reducePow] at *
  have hx : ((i % 4294967296 : Nat) : Int) < 4294967296 := by omega
  have hx0 : (0 : Int) ≤ ((i % 4294967296 : Nat) : Int) := by omega
  have e1 : (i % 4294967296 < 2147483648) ↔ ((i % 4294967296 : Nat) : Int) < 2147483648 := by
    omega
  simp only [e1]
  generalize ((i % 4294967296 : Nat) : Int) = x at *
  split_ifs with h1 h2
  · rw [mulhi_pos _ (by omega) (by omega), sign_fix _ (by omega) (by omega)]
    split_ifs <;> omega
  · omega
  · rw [mulhi_neg _ (by omega) (by omega), sign_fix _ (by omega) (by omega)]
    split_ifs <;> omega

theorem remI_range (i : Nat) : -2 ≤ remI i ∧ remI i ≤ 2 := by
  unfold remI quoI sxI
  split_ifs <;> omega

theorem ofNat_toNat64 (x : BitVec 64) : x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- `%r144` for every counter: `32768 · remI i` modulo `2 ^ 32`. -/
theorem slotKW_toNat (i : Nat) : ((slotKW i).toNat : Int) = 32768 * remI i % 2 ^ 32 := by
  have hq := quotW_toNat i
  have hqn := (quotW i).isLt
  unfold slotKW madLoW
  rw [ofNat_toNat64 (quotW i)]
  generalize (quotW i).toNat = Q at hq hqn ⊢
  nf_simp
  unfold remI
  unfold quoI sxI at hq ⊢
  push_cast
  split_ifs at hq ⊢ <;> omega

/-- `%r140` for every counter: `8 · remI i` modulo `2 ^ 32`. -/
theorem slotW_toNat (i : Nat) : ((slotW i).toNat : Int) = 8 * remI i % 2 ^ 32 := by
  have hq := quotW_toNat i
  have hqn := (quotW i).isLt
  unfold slotW madLoW
  rw [ofNat_toNat64 (quotW i)]
  generalize (quotW i).toNat = Q at hq hqn ⊢
  nf_simp
  unfold remI
  unfold quoI sxI at hq ⊢
  push_cast
  split_ifs at hq ⊢ <;> omega

/-- The tile slot offset the code computes from the counter, as a number below `2 ^ 32`. -/
def kOff (i : Nat) : Nat := (slotKW i).toNat

/-- The barrier slot offset the code computes from the counter. -/
def bOff (i : Nat) : Nat := (slotW i).toNat

/-- The parity of the `kv_empty` poll the code computes from the counter. -/
def parW (i : Nat) : Nat := (andW (notW (quotW i)) (BitVec.ofInt 64 1)).toNat

theorem kOff_eq {i : Nat} (hi : i < 2 ^ 31) : kOff i = 32768 * (i % 3) := by
  unfold kOff
  rw [slotKW_eq hi]
  simp only [BitVec.toNat_ofNat]
  omega

theorem bOff_eq {i : Nat} (hi : i < 2 ^ 31) : bOff i = 8 * (i % 3) := by
  unfold bOff
  rw [slotW_eq hi]
  simp only [BitVec.toNat_ofNat]
  omega

theorem parW_eq {i : Nat} (hi : i < 2 ^ 31) : parW i = 1 - i / 3 % 2 := by
  unfold parW
  rw [parity_eq hi]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The tile slot offset for every counter: `32768 r` modulo `2 ^ 32`, `r ∈ {-2, …, 2}`. -/
theorem kOff_cases (i : Nat) :
    kOff i = 0 ∨ kOff i = 32768 ∨ kOff i = 65536 ∨ kOff i = 2 ^ 32 - 32768 ∨
      kOff i = 2 ^ 32 - 65536 := by
  have h := slotKW_toNat i
  have hr := remI_range i
  unfold kOff
  generalize remI i = r at h hr
  omega

/-- The barrier slot offset for every counter: `8 r` modulo `2 ^ 32`, `r ∈ {-2, …, 2}`. -/
theorem bOff_cases (i : Nat) :
    bOff i = 0 ∨ bOff i = 8 ∨ bOff i = 16 ∨ bOff i = 2 ^ 32 - 8 ∨ bOff i = 2 ^ 32 - 16 := by
  have h := slotW_toNat i
  have hr := remI_range i
  unfold bOff
  generalize remI i = r at h hr
  omega

/-- A register of the tile ring for every counter: the shared base plus the slot offset plus `c`,
modulo `2 ^ 32`. -/
theorem kvc_word (L : Launch) (i c : Nat) :
    addW (kvW L i) (BitVec.ofInt 64 (c : Int)) =
      BitVec.ofNat 64 ((L.sharedBase + kOff i + c) % 2 ^ 32) := by
  have hk := (slotKW i).isLt
  unfold kvW baseW kOff
  rw [ofNat_toNat64 (slotKW i)]
  generalize (slotKW i).toNat = K at hk ⊢
  unfold addW
  nf_simp
  omega

theorem kv_word (L : Launch) (i : Nat) :
    kvW L i = BitVec.ofNat 64 ((L.sharedBase + kOff i) % 2 ^ 32) := by
  have hk := (slotKW i).isLt
  unfold kvW baseW kOff
  rw [ofNat_toNat64 (slotKW i)]
  generalize (slotKW i).toNat = K at hk ⊢
  unfold addW
  nf_simp
  omega

/-- A barrier register of the iteration for every counter. -/
theorem barc_word (L : Launch) (i c : Nat) :
    addW (barW L i) (BitVec.ofInt 64 (c : Int)) =
      BitVec.ofNat 64 ((L.sharedBase + bOff i + c) % 2 ^ 32) := by
  have hk := (slotW i).isLt
  unfold barW baseW bOff
  rw [ofNat_toNat64 (slotW i)]
  generalize (slotW i).toNat = K at hk ⊢
  unfold addW
  nf_simp
  omega

theorem parW_lt (i : Nat) : parW i < 2 := by
  unfold parW andW
  simp only [rdW, truncBits, BitVec.toNat_ofNat, BitVec.toNat_and]
  have h1 : (BitVec.ofInt 64 1).toNat % 2 ^ 32 % 2 ^ 64 = 1 := by decide
  rw [h1]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

end
end PTX.Kernels.InklingRelDecode.Proof.Loader
