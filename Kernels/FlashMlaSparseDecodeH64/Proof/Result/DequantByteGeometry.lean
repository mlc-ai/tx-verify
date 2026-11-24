-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmKvValues
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputStageReuse
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # Invert the shared layout of the KV operands -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open MmaDataTrace Protocol OutputStageReuse

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- A stored dequantization byte is the swizzled byte of its logical token and feature. -/
theorem logical_store_byte (hpre : Pre P L mem0)
    (cta : Nat) (lane : Fin 128) (block : Nat) (row : Fin 4) (step : Fin 8) (b : Fin 16) :
    let g := GemmRing.producer L cta lane
    (dequantStoreByte L cta lane (block % 2) row step b).addr =
      TensorSwizzle.offset .b128 0
        (kvLinearByte L block (Wg2.rawRow L g row.val)
          (Wg2.logicalElem L g step.val (b.val / 2)) (b.val % 2)) := by
  dsimp only
  let g := GemmRing.producer L cta lane
  let j : Fin 8 := ⟨b.val / 2, by have := b.isLt; omega⟩
  let k : Fin 2 := ⟨b.val % 2, by omega⟩
  change (_ : Nat) = TcShared.Swizzle.offset .b128
    (kvLinearByte L block (Wg2.rawRow L g row.val) (Wg2.logicalElem L g step.val j.val) k.val)
  rw [dequantized_mmaByte hpre]
  simp only [dequantStoreByte, g, j, k]
  omega

/-- The exact byte fixes the dequantizer lane, row, step, and physical slot. -/
theorem dequant_store_coordinates (hpre : Pre P L mem0)
    {cta block block' : Nat} {lane : Fin 128} {row : Fin 4} {step : Fin 8} {sub : Fin 16}
    {slot : Fin 64} {feature : Fin 512} {b : Fin 2}
    (he : dequantStoreByte L cta lane (block' % 2) row step sub =
      ⟨.shared, cta, TensorSwizzle.offset .b128 0
        (kvLinearByte L block slot.val feature.val b.val)⟩) :
    block' % 2 = block % 2 ∧ lane = dequantLane slot feature ∧
      row.val = slot.val / 16 ∧ step.val = feature.val / 64 ∧
      sub.val = 2 * (feature.val % 8) + b.val := by
  let g := GemmRing.producer L cta lane
  have hl := lane.isLt
  have hr := row.isLt
  have hs := step.isLt
  have hb := sub.isLt
  have hslot := slot.isLt
  have hf := feature.isLt
  have hbyte := b.isLt
  have ht : tidOf L g = 256 + lane.val := by
    simp only [g, RawRing.consumer, tidOf_eq hpre, hpre.block]
    omega
  have hAddr := congrArg Loc.addr he
  rw [logical_store_byte hpre] at hAddr
  have hlinear := TensorSwizzle.offset_injective .b128 0 hAddr
  change kvLinearByte L block' (Wg2.rawRow L g row.val)
    (Wg2.logicalElem L g step.val (sub.val / 2)) (sub.val % 2) =
      kvLinearByte L block slot.val feature.val b.val at hlinear
  simp only [kvLinearByte, Wg1Mma.kvBase, Wg2.rawRow, Wg2.groupIdx, Wg2.idxInWg,
    Wg2.logicalElem, Wg2.idxInGroup, ht, Wg2.numGroups, Wg2.groupSize,
    Wg2.elemsPerStep, Wg2.rawBytesPerThread] at hlinear
  have hBlock : block' % 2 = block % 2 := by omega
  have hRow : 16 * row.val + lane.val / 8 = slot.val := by omega
  have hFeature : 64 * step.val + 8 * (lane.val % 8) + sub.val / 2 = feature.val := by
    omega
  have hByte : sub.val % 2 = b.val := by omega
  exact ⟨hBlock, Fin.ext (by simp only [dequantLane]; omega), by omega, by omega, by omega⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
