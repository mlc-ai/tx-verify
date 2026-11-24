-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualMaskWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GatherWord

@[expose] public section

/-! # The gathered block's logical mask, weights, and values -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open Wg1Mma
noncomputable section

private theorem slotPos_blockSlot (P : Params) (batch block pos : Nat) :
    slotPos (P.topkLen batch) block (pos / 2) (pos % 2) = blockSlot P batch block pos := by
  have hExtra : blockExtra P batch block =
      FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen batch) := rfl
  have hOrig : origBlocks P batch = FlashMlaSparseDecodeH64.numOrigBlocks (P.topkLen batch) :=
    rfl
  rw [blockSlot, hExtra, hOrig]
  unfold slotPos
  split_ifs <;> dsimp only [FlashMlaSparseDecodeH64.topkBlock, Result.topkBlock] <;> omega

/-- The Boolean used by the index warp is the specification's slot validity for that block. -/
theorem gatheredValid_spec (P : Params) (L : Launch) (g block pos : Nat) :
    let batch := batchOf L g
    let query := queryOf L g
    gatheredValid P L g block pos = decide
      (slotValid P batch query (blockExtra P batch block) (blockSlot P batch block pos)) := by
  dsimp only
  apply Bool.eq_iff_iff.mpr
  have hExtra : blockExtra P (batchOf L g) block =
      FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen (batchOf L g)) := rfl
  simp only [gatheredValid, Wg1Tma.validBit, kvSlotValid, Wg1Tma.slotIdx,
    Wg1Tma.eOf, Wg1Tma.qOf, ← batchOf_eq_ctaidY, ← queryOf_eq_ctaidX, slotIndex,
    slotPos_blockSlot, slotLen, slotValid, hExtra, Bool.and_eq_true, decide_eq_true_eq]
  simp [bne_iff_ne, and_comm]
  intro _
  rfl

/-- A valid slot's gathered raw bytes are exactly the row selected by the specification. -/
theorem gatheredRow_spec (P : Params) (L : Launch) (g block pos : Nat)
    (hvalid : gatheredValid P L g block pos = true) :
    Wg2.gatheredByte P L g block pos =
      rowBytes P (batchOf L g) (queryOf L g) (blockExtra P (batchOf L g) block)
        (blockSlot P (batchOf L g) block pos) := by
  funext off
  unfold Wg2.gatheredByte
  change (if gatheredValid P L g block pos = true then _ else _) = _
  rw [ite_eq_left hvalid]
  simp only [Wg1Tma.eOf, Wg1Tma.qOf, batchOf_eq_ctaidY, queryOf_eq_ctaidX, slotPos_blockSlot]
  rfl

/-- The actual block's shifted probability is the unnormalized specification weight scaled
by the inverse of the reference. Padded and invalid slots contribute zero. -/
theorem gathered_probability_spec (P : Params) (L : Launch) (g head block pos : Nat) (ref : ℝ) :
    blockProbability P L g head ref (Wg2.gatheredByte P L g block)
      (gatheredValid P L g block) pos =
      2 ^ (-ref) * blockWeight P (batchOf L g) (queryOf L g) head block pos := by
  have h := gatheredValid_spec P L g block pos
  dsimp only at h
  by_cases hv : slotValid P (batchOf L g) (queryOf L g)
      (blockExtra P (batchOf L g) block) (blockSlot P (batchOf L g) block pos)
  · have hBit : gatheredValid P L g block pos = true := h.trans (decide_eq_true hv)
    have hb := gatheredRow_spec P L g block pos hBit
    have hScore : blockDot P L g head pos (Wg2.gatheredByte P L g block) =
        score P (batchOf L g) (queryOf L g) head (blockExtra P (batchOf L g) block)
          (blockSlot P (batchOf L g) block pos) := by
      unfold blockDot score slotValue
      rw [hb]
    unfold blockProbability blockScore
    rw [ite_eq_left hBit, hScore]
    change shiftedWeight P.scale ref (some _) = _
    rw [shiftedWeight_fin, blockWeight, weight, ite_eq_left hv]
    exact mul_comm _ _
  · have hBit : gatheredValid P L g block pos = false := h.trans (decide_eq_false_iff_not.mpr hv)
    have hZero : shiftedWeight P.scale ref (⊥ : WithBot ℝ) = 0 :=
      (shiftedWeight_zero P.scale ref ⊥).mpr rfl
    simp [blockProbability, blockScore, hBit, hZero, blockWeight, weight, hv]

/-- A PV term agrees with the corresponding term of the specification numerator, including
the slots that the gather zero-fills. -/
theorem gathered_pv_term_spec (P : Params) (L : Launch) (g head block pos feature : Nat) (ref : ℝ) :
    blockProbability P L g head ref (Wg2.gatheredByte P L g block)
      (gatheredValid P L g block) pos * dequant (Wg2.gatheredByte P L g block pos) feature =
      2 ^ (-ref) * (blockWeight P (batchOf L g) (queryOf L g) head block pos *
        blockValue P (batchOf L g) (queryOf L g) block pos feature) := by
  rw [gathered_probability_spec, mul_assoc]
  have h := gatheredValid_spec P L g block pos
  dsimp only at h
  by_cases hv : slotValid P (batchOf L g) (queryOf L g)
      (blockExtra P (batchOf L g) block) (blockSlot P (batchOf L g) block pos)
  · have hBit : gatheredValid P L g block pos = true := h.trans (decide_eq_true hv)
    rw [gatheredRow_spec P L g block pos hBit]
    rfl
  · simp [blockWeight, weight, hv]

/-- The sum of an actual PV contraction has the order and scaling used by the run. -/
theorem gathered_pv_sum_spec (P : Params) (L : Launch) (g head block feature : Nat) (ref : ℝ) :
    (∑ s ∈ Finset.range 64, blockProbability P L g head ref (Wg2.gatheredByte P L g block)
      (gatheredValid P L g block) s * dequant (Wg2.gatheredByte P L g block s) feature) =
    ∑ s ∈ Finset.range topkBlock,
      blockWeight P (batchOf L g) (queryOf L g) head block s * 2 ^ (-ref) *
        blockValue P (batchOf L g) (queryOf L g) block s feature := by
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [gathered_pv_term_spec, ← mul_assoc, mul_comm ((2 : ℝ) ^ (-ref))]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
