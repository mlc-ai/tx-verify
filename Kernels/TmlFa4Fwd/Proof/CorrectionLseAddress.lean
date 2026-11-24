-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseStore
import Kernels.TmlFa4Fwd.Flow.Code.Part141
public import Lemmas.Flow.Footprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem signedPositive {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left h]

private theorem subtractWord {q start : Nat} (hQ : q < 2 ^ 32) (hStart : start ≤ q) :
    BitVec.ofNat 64 q - BitVec.ofNat 64 start = BitVec.ofNat 64 (q - start) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt (show q < 2 ^ 64 by omega),
    toNat_ofNat_lt (show start < 2 ^ 64 by omega),
    toNat_ofNat_lt (show q - start < 2 ^ 64 by omega)]
  omega

/-- The first LSE tail compare computes the signed row test against the live tile's length. -/
theorem lseFirstTail {l : Launch} {g len tile row : Nat}
    (hLength : len < 2 ^ 31) (hTile : 256 * tile < len) (hRow : row < 128) :
    Seg kernel [] l g 2 9065
      [(1635, b32 len), (5967, b32 (256 * tile)), (1613, b32 row)] 9067
      [(741, .pred (decide (len ≤ 256 * tile + row))),
        (7077, b32 (len - 256 * tile)), (5967, b32 (256 * tile)), (1613, b32 row)] := by
  intro t ht
  have hLen32 : len < 2 ^ 32 := by omega
  have hTile32 : 256 * tile < 2 ^ 32 := by omega
  have hRow32 : row < 2 ^ 32 := by omega
  have hRem32 : len - 256 * tile < 2 ^ 32 := by omega
  have hRowSigned : row < 2 ^ 31 := by omega
  have hRemSigned : len - 256 * tile < 2 ^ 31 := by omega
  have hSub := subtractWord hLen32 hTile.le
  seg_fp ht using
    simp only [b32, truncBits_ofNat hLen32 (by decide), truncBits_ofNat hTile32 (by decide),
      truncBits_ofNat hRow32 (by decide), hSub, truncBits_ofNat hRem32 (by decide),
      compare, Option.getD_some, signedPositive hRowSigned, signedPositive hRemSigned,
      Value.pred.injEq, decide_eq_decide]
    all_goals omega

private def remainingWord (remaining : Nat) : Nat := (remaining + 2 ^ 32 - 128) % 2 ^ 32

private theorem remainingSigned {remaining : Nat} (h : remaining < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 (remainingWord remaining)) = (remaining : Int) - 128 := by
  have h32 : remainingWord remaining < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [toSigned, toNat_ofNat_lt (show remainingWord remaining < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h32]
  unfold remainingWord
  split <;> omega

private theorem remainingAdd {remaining : Nat} (h : remaining < 2 ^ 31) :
    truncBits 32 (BitVec.ofNat 64 remaining + truncBits 32 (BitVec.ofInt 64 (-128))) =
      BitVec.ofNat 64 (remainingWord remaining) := by
  have hImm : truncBits 32 (BitVec.ofInt 64 (-128)) = BitVec.ofNat 64 (2 ^ 32 - 128) := rfl
  rw [hImm, ← BitVec.ofNat_add, truncBits, toNat_ofNat_lt (by omega)]
  have hs : remaining + (2 ^ 32 - 128) = remaining + 2 ^ 32 - 128 := by omega
  rw [hs]
  rfl

/-- In the second half the hardware subtracts 128 before comparing. This includes tiles
shorter than 128 rows, where the signed remainder is negative and every store is skipped. -/
theorem lseSecondTail {l : Launch} {g len tile row : Nat}
    (hLength : len < 2 ^ 31) (hTile : 256 * tile < len) (hRow : row < 128) :
    Seg kernel [] l g 2 9079 [(7077, b32 (len - 256 * tile)), (1613, b32 row)] 9081
      [(743, .pred (decide (len ≤ 256 * tile + 128 + row)))] := by
  intro t ht
  have hRem : len - 256 * tile < 2 ^ 31 := by omega
  have hRem32 : len - 256 * tile < 2 ^ 32 := by omega
  have hRow32 : row < 2 ^ 32 := by omega
  have hRowSigned : row < 2 ^ 31 := by omega
  have h32 : remainingWord (len - 256 * tile) < 2 ^ 32 := Nat.mod_lt _ (by decide)
  seg_fp ht using
    simp only [truncBits_ofNat hRem32 (by decide), truncBits_ofNat hRow32 (by decide),
      remainingAdd hRem, truncBits_ofNat h32 (by decide), compare, Option.getD_some,
      signedPositive hRowSigned, remainingSigned hRem, Value.pred.injEq, decide_eq_decide]
    all_goals omega

/-- The base of this sequence within its packed head is the ABI LSE pointer plus the
byte-scaled head stride and cumulative query index. -/
theorem lsePackedBase {p : Params} {l : Launch} {g head batch : Nat}
    (hOffset : p.qOffset batch < 2 ^ 31) (hHead : head < 2 ^ 64)
    (hStride : p.lseStride < 2 ^ 64) (hAddr : (p.lseLoc (p.qOffset batch) head).addr < 2 ^ 64) :
    Seg kernel [] l g 4 9057
      [(1634, b32 (p.qOffset batch)), (9605, b64 head), (7501, b64 p.lseStride),
       (7500, b64 p.lseBase)] 9061 [(9525, b64 (p.lseLoc (p.qOffset batch) head).addr)] := by
  intro t ht
  have hBase : p.lseBase + 4 * (head * p.lseStride + p.qOffset batch) < 2 ^ 64 := hAddr
  have hOffset32 : p.qOffset batch < 2 ^ 32 := by omega
  have hMod : p.qOffset batch % 4294967296 = p.qOffset batch := Nat.mod_eq_of_lt hOffset32
  have hh : head % 18446744073709551616 = head := Nat.mod_eq_of_lt hHead
  have hs : p.lseStride % 18446744073709551616 = p.lseStride := Nat.mod_eq_of_lt hStride
  seg_fp ht using
    norm_bits [Params.lseLoc, globalLoc, hMod, cvtIntBits, intBits, intSat, intOf, Bool.not_false,
      signedPositive hOffset, hh, hs, BitVec.ofInt_natCast]

/-- A row within a 256-row tile has disjoint low bits, so the checked OR in the
address arithmetic implements addition of the row to the tile base. -/
theorem lseRowAddress {p : Params} {l : Launch} {g head batch tile row : Nat}
    (hTile : 256 * tile < 2 ^ 31) (hRow : row < 128) :
    Seg kernel [] l g 5 9067
      [(5967, b32 (256 * tile)), (1613, b32 row),
       (9525, b64 (p.lseLoc (p.qOffset batch) head).addr)] 9072
      [(7491, b64 (p.lseLoc (p.qOffset batch + 256 * tile + row) head).addr)] := by
  intro t ht
  have hTile32 : 256 * tile < 2 ^ 32 := by omega
  have hRow32 : row < 2 ^ 32 := by omega
  have hTile64 : 256 * tile < 2 ^ 64 := by omega
  have hRow64 : row < 2 ^ 64 := by omega
  have hTileMod : 256 * tile % 4294967296 = 256 * tile := Nat.mod_eq_of_lt hTile32
  have hRowMod : row % 4294967296 = row := Nat.mod_eq_of_lt hRow32
  have hTileWide : 256 * tile % 18446744073709551616 = 256 * tile := Nat.mod_eq_of_lt hTile64
  have hRowWide : row % 18446744073709551616 = row := Nat.mod_eq_of_lt hRow64
  have hOr : 256 * tile ||| row = 256 * tile + row :=
    (Nat.two_pow_add_eq_or_of_lt (i := 8) (show row < 2 ^ 8 by omega) tile).symm
  seg_fp ht using
    norm_bits [Params.lseLoc, globalLoc, hTileMod, hRowMod, cvtIntBits, intBits, intSat, intOf,
      Bool.not_false, signedPositive hTile, BitVec.ofInt_natCast,
      hTileWide, hRowWide, hOr]

end
end PTX.Kernels.TmlFa4Fwd.Correction
