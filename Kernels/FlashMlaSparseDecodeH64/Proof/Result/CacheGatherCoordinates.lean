-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmRawInput

@[expose] public section

/-! # Signed gather coordinates and their logical cache slots -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather

open Wg1Tma

/-- A valid TMA coordinate slot names a valid selected slot in the functional specification. -/
theorem coord_valid_slot {P : Params} {L : Launch} {g block pos : Nat}
    (hv : validBit P L g block (pos / 2) (pos % 2) = true) :
    slotValid P (eOf L g) (qOf L g)
      (FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (eOf L g)))
      (slotPos (P.topkLen (eOf L g)) block (pos / 2) (pos % 2)) := by
  have hh := kvSlotValid_eq_true_iff.mp hv
  unfold slotValid
  simpa only [slotLen, slotIdx, slotIndex, and_comm] using hh

/-- The signed gather marker for a rejected sparse slot is minus one. -/
theorem coord_signed_invalid {P : Params} {L : Launch} {g block pos : Nat}
    (hv : validBit P L g block (pos / 2) (pos % 2) = false) :
    (BitVec.ofNat 32 (coordAt P L g block pos)).toInt = -1 := by
  rw [coordAt_invalid hv]
  decide

/-- A valid main-cache coordinate is the exact physical row, in signed range and tensor range. -/
theorem coord_signed_main {P : Params} {L : Launch} {mem0 : Mem0} {g block pos : Nat}
    (hpre : Pre P L mem0)
    (he : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hb : block < FlashMlaSparseDecodeH64.totalBlocks
      (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hm : FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (eOf L g)) = false)
    (hv : validBit P L g block (pos / 2) (pos % 2) = true) :
    let j := slotPos (P.topkLen (eOf L g)) block (pos / 2) (pos % 2)
    let r := tokenRow P.page P.blockStride (P.idx (eOf L g) (qOf L g) j)
    (BitVec.ofNat 32 (coordAt P L g block pos)).toInt = ↑r ∧
      r < P.numBlocks * (P.blockStride / 528) := by
  intro j r
  have hs := coord_valid_slot hv
  rw [hm] at hs
  have hidx := (hpre.idxRange _ he _ hq _ hs).2
  have hpage : P.page ≤ P.blockStride / 528 := by
    have := hpre.pageFits
    omega
  have hCoord := coordAt_rowOf hpre he hq hb hv
  rw [hCoord]
  simp only [slotStride, slotPg, slotIdx, slotBlockStride, slotPage, slotIndex]
  have hm' : ¬ FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (eOf L g)) = true := by
    rw [hm]
    decide
  rw [ite_eq_right hm', ite_eq_right hm', ite_eq_right hm']
  exact ⟨signed_row hpre.pagePos hpage hidx hpre.rowsRange, rowOf_lt hpre.pagePos hpage hidx⟩

/-- A valid extra-cache coordinate is the exact physical row, in signed range and tensor range. -/
theorem coord_signed_extra {P : Params} {L : Launch} {mem0 : Mem0} {g block pos : Nat}
    (hpre : Pre P L mem0)
    (he : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hb : block < FlashMlaSparseDecodeH64.totalBlocks
      (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hm : FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (eOf L g)) = true)
    (hv : validBit P L g block (pos / 2) (pos % 2) = true) :
    let j := slotPos (P.topkLen (eOf L g)) block (pos / 2) (pos % 2)
    let r := tokenRow P.extraPage P.extraBlockStride (P.extraIdx (eOf L g) (qOf L g) j)
    (BitVec.ofNat 32 (coordAt P L g block pos)).toInt = ↑r ∧
      r < P.extraNumBlocks * (P.extraBlockStride / 528) := by
  intro j r
  have hs := coord_valid_slot hv
  rw [hm] at hs
  have hidx := (hpre.extraIdxRange _ he _ hq _ hs).2
  have hlen := extraLen_le hpre he
  have hpos : 0 < P.extra_topk := by
    have : j < P.extraTopkLen (eOf L g) := hs.1
    omega
  obtain ⟨hp, _, _, hfit⟩ := hpre.extraPos hpos
  have hpage : P.extraPage ≤ P.extraBlockStride / 528 := by omega
  have hCoord := coordAt_rowOf hpre he hq hb hv
  rw [hCoord]
  simp only [slotStride, slotPg, slotIdx, slotBlockStride, slotPage, slotIndex]
  rw [ite_eq_left hm, ite_eq_left hm, ite_eq_left hm]
  exact ⟨signed_row hp hpage hidx hpre.extraRowsRange, rowOf_lt hp hpage hidx⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather
