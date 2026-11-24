-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Flow.Code.Part033

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

private theorem int32Signed {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  simp only [toSigned, toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32, ite_eq_left h]

private theorem lowSevenMask {x : Nat} (hx : x < 2 ^ 32) :
    x &&& 4294967168 = x / 128 * 128 := by
  have hDiv : (x &&& 4294967168) / 128 = x / 128 := by
    rw [show 128 = 2 ^ 7 from rfl, Nat.and_div_two_pow]
    change x / 128 &&& (2 ^ 25 - 1) = x / 128
    exact Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)
  have hMod : (x &&& 4294967168) % 128 = 0 := by
    rw [show 128 = 2 ^ 7 from rfl, Nat.and_mod_two_pow]
    simp
  omega

private structure CeilSite where
  pc : Nat
  lengthReg : Nat
  quotient : Nat
  remainder : Nat
  count : Nat

private def ceilSite : Fin 2 → CeilSite
  | 0 => ⟨2117, 2541, 2545, 378, 2548⟩
  | 1 => ⟨2129, 2550, 2554, 381, 2557⟩

private theorem blockCount (site : Fin 2) (l : Launch) (g : Nat) {len : Nat}
    (hlen : len < 2 ^ 31) :
    Seg kernel [] l g 10 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 10) [((ceilSite site).count, b32 ((len + 127) / 128))] := by
  have h32 : len < 2 ^ 32 := by omega
  have h64 : len < 2 ^ 64 := by omega
  have hx64 : len < 18446744073709551616 := h64
  have hDiv : len / 128 < 2 ^ 32 := by omega
  have hMask : len / 128 * 128 < 2 ^ 32 := by omega
  have shr31 : (len : Int) / 2 ^ 31 = 0 := by omega
  have shr7 : (len : Int) / 2 ^ 7 = (len / 128 : Nat) := by omega
  have s31 : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := rfl
  have s7 : min (truncBits 32 (BitVec.ofInt 64 7)).toNat 32 = 7 := rfl
  have s25 : (truncBits 32 (BitVec.ofInt 64 25)).toNat = 25 := rfl
  have z : truncBits 32 (BitVec.ofInt 64 0) = 0 := rfl
  have z32 : truncBits 32 0 = 0 := rfl
  have zShift : (0 : BitVec 64) >>> 25 = 0 := rfl
  have h25 : ¬25 ≥ 32 := by decide
  have hNeg : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 := rfl
  have hPos : (-1 : Int) < len := by omega
  have m32 : truncBits 32 (BitVec.ofInt 64 (-128)) = BitVec.ofNat 64 4294967168 := rfl
  have aZero : BitVec.ofNat 64 len + 0 = BitVec.ofNat 64 len := BitVec.add_zero _
  have hFirst : Seg kernel [] l g 8 (ceilSite site).pc [((ceilSite site).lengthReg, b32 len)]
      ((ceilSite site).pc + 8)
      [((ceilSite site).quotient, b32 (len / 128)),
       ((ceilSite site).remainder, .pred (decide (len ≠ len / 128 * 128)))] := by
    fin_cases site <;> intro t ht <;> seg_fp ht using
      simp only [b32, s31, s7, s25, ite_eq_right h25, shr31, shr7, z, z32, zShift,
        aZero, truncBits_ofNat h32 (by decide), m32,
        truncBits_ofNat hDiv (by decide), BitVec.ofInt_natCast, nf_and, compare,
        Option.getD_some, int32Signed hlen, hNeg, gt_iff_lt, hPos, decide_true, Bool.true_and,
        toNat_ofNat_lt h64, Int.ofNat_inj, ne_eq]
      all_goals
        simp only [Nat.mod_eq_of_lt hx64, Nat.reduceMod, lowSevenMask h32,
          truncBits_ofNat hMask (by decide),
          toNat_ofNat_lt (show len / 128 * 128 < 2 ^ 64 by omega)]
  have hLast : Seg kernel [] l g 2 ((ceilSite site).pc + 8)
      [((ceilSite site).quotient, b32 (len / 128)),
       ((ceilSite site).remainder, .pred (decide (len ≠ len / 128 * 128)))]
      ((ceilSite site).pc + 10) [((ceilSite site).count, b32 ((len + 127) / 128))] := by
    by_cases h : len = len / 128 * 128
    · have hPad : decide (len ≠ len / 128 * 128) = false := decide_eq_false (fun hn => hn h)
      fin_cases site <;> intro t ht <;> simp only [hPad] at ht <;> seg_fp ht using norm_bits
    · fin_cases site <;> intro t ht <;>
        simp only [decide_eq_true h] at ht <;> seg_fp ht using norm_bits
  exact hFirst.comp hLast

/-- Ceiling division of the key length as decoded at PC 2117. -/
theorem keyBlockCount (l : Launch) (g : Nat) {len : Nat} (hlen : len < 2 ^ 31) :
    Seg kernel [] l g 10 2117 [(2541, b32 len)] 2127 [(2548, b32 ((len + 127) / 128))] :=
  blockCount 0 l g hlen

/-- Ceiling division after correcting the key length by the causal query position. -/
theorem causalBlockCount (l : Launch) (g : Nat) {len : Nat} (hlen : len < 2 ^ 31) :
    Seg kernel [] l g 10 2129 [(2550, b32 len)] 2139 [(2557, b32 ((len + 127) / 128))] :=
  blockCount 1 l g hlen

/-- The two signed additions fold the query-end displacement into the K length. -/
theorem causalLength (l : Launch) (g : Nat) {k q queryEnd : Nat}
    (hk : k < 2 ^ 31) (hq : q ≤ k) (hEnd : queryEnd < 2 ^ 31)
    (_hSum : k - q + queryEnd < 2 ^ 31) :
    Seg kernel [] l g 2 2127 [(2541, b32 k), (7202, b32 queryEnd), (2540, b32 (2^32 - q))]
      2129 [(2550, b32 (k - q + queryEnd))] := by
  intro t ht
  seg_fp ht using
    norm_bits

/-- The MMA loop count is the smaller of the two decoded block counts. -/
theorem firstPollCount (l : Launch) (g : Nat) {keys causal : Nat}
    (hk : keys < 2 ^ 31) (hc : causal < 2 ^ 31) :
    Seg kernel [] l g 2 2139 [(2548, b32 keys), (2557, b32 causal)]
      2141 [(1189, b32 (min keys causal)), (2536, b32 0)] := by
  have h32k : keys < 2 ^ 32 := by omega
  have h32c : causal < 2 ^ 32 := by omega
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  by_cases h : keys < causal
  · intro t ht
    seg_fp ht using
      (simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32c (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hk, int32Signed hc,
        Int.ofNat_lt, h, decide_true, ↓reduceIte,
        min_eq_left h.le]
       try rfl)
  · have hle : causal ≤ keys := by omega
    intro t ht
    seg_fp ht using
      (simp only [hMin, b32, truncBits_ofNat h32k (by decide), truncBits_ofNat h32c (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hk, int32Signed hc,
        Int.ofNat_lt, h, decide_false, ↓reduceIte,
        min_eq_right hle]
       try rfl)

end PTX.Kernels.TmlFa4Fwd.Mma
