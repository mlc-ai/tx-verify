-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow MmaDataTrace

noncomputable section

/-- Each BF16 half of the four-byte P store is exactly the byte addressed by the
corresponding logical head and sparse slot of the PV operand. -/
theorem pStore_mmaByte {L : Launch} {g block : Nat}
    (hh : Wg0.head L g = Proof.laneOf L g + 32 * (Proof.warpOf L g % 2))
    (k sub : Fin 4) (half byte : Fin 2) :
    ∃ loc, Wg0.siteLoc L g (.pStore k) block sub.val = some loc ∧
      loc.at (2 * half.val + byte.val) =
        ⟨.shared, Proof.ctaOf L g, pLinearByte L (Wg0.head L g)
          (32 * Wg0.half L g + 2 * (4 * k.val + sub.val) + half.val) byte.val⟩ := by
  refine ⟨_, rfl, ?_⟩
  simp only [Wg0.shLoc, Loc.at, pLinearByte, Wg0.pTileBase,
    Wg0.pChunkStride, Wg0.half, hh]
  congr 1
  omega

/-- Packed probability bytes retain the two individual BF16 payloads written by the lane. -/
theorem pPacked_mmaByte (L : Launch) (g : Nat) (d : Wg0.D) (k sub : Fin 4)
    (half byte : Fin 2) :
    (Wg0.pPacked L g d (4 * k.val + sub.val)).toBytes[2 * half.val + byte.val]? =
      some (.float .bf16 (d.pw (Wg0.head L g)
        (32 * Wg0.half L g + 2 * (4 * k.val + sub.val) + half.val)), byte.val) := by
  fin_cases half <;> fin_cases byte <;> rfl

/-- The absolute B128 swizzle used by both MMA B descriptors agrees with the dequantizer's
explicit XOR of a lane's 16-byte chunk by the row within its swizzle atom. -/
theorem dequantized_mmaByte {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (block g : Nat) (r : Fin 4) (step elem : Fin 8) (byte : Fin 2) :
    TcShared.Swizzle.offset .b128
      (kvLinearByte L block (Wg2.rawRow L g r.val) (Wg2.logicalElem L g step.val elem.val)
        byte.val) =
    L.sharedBase + Wg2.tileBase (block % 2) + Wg2.tileOff L g r.val step.val +
      2 * elem.val + byte.val := by
  let base := L.sharedBase + Wg2.tileBase (block % 2)
  let row := Wg2.rawRow L g r.val
  let lane := Wg2.idxInGroup L g
  let n := base + 128 * row + 8192 * step.val + 16 * lane + 2 * elem.val + byte.val
  have ha : base % 1024 = 0 := by
    have h := hpre.sharedAlignment
    dsimp [base, Wg2.tileBase, Wg2.dequantBytes]
    rw [hpre.sharedBase]
    omega
  have hLane : lane < 8 := Wg2.idxInGroup_lt L g
  have hElem := elem.isLt
  have hByte := byte.isLt
  have hx : kvLinearByte L block row (Wg2.logicalElem L g step.val elem.val) byte.val = n := by
    have hv : Wg2.logicalElem L g step.val elem.val = 64 * step.val + 8 * lane + elem.val := by
      simp [Wg2.logicalElem, Wg2.elemsPerStep, Wg2.rawBytesPerThread, lane, Nat.mul_comm]
    rw [hv]
    dsimp [kvLinearByte, n, base, Wg2.tileBase, Wg2.dequantBytes, Wg1Mma.kvBase]
    omega
  have h128 : n / 128 = base / 128 + row + 64 * step.val := by dsimp [n]; omega
  have h16 : n / 16 % 8 = lane := by dsimp [n]; omega
  have hb : n % 16 = 2 * elem.val + byte.val := by dsimp [n]; omega
  have hrow : n / 128 % 8 = Wg2.rowInAtom L g := by
    rw [h128]
    dsimp [row, Wg2.rawRow, Wg2.numGroups, Wg2.rowInAtom]
    omega
  change TcShared.Swizzle.offset .b128
    (kvLinearByte L block row (Wg2.logicalElem L g step.val elem.val) byte.val) = _
  rw [hx]
  change TensorSwizzle.offset .b128 0 n = _
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, Nat.zero_div, Nat.zero_add, BitVec.toNat_xor, BitVec.toNat_ofNat]
  change 128 * (n / 128) + 16 * (n / 16 % 8 ^^^ (n / 128 % 8) % 8) + n % 16 = _
  rw [h128, h16, hb]
  have hr0 := Wg2.rowInAtom_lt L g
  have hr' : (base / 128 + row + 64 * step.val) % 8 = Wg2.rowInAtom L g :=
    h128 ▸ hrow
  rw [hr', Nat.mod_eq_of_lt hr0]
  dsimp [base, row, lane, Wg2.tileOff, Wg2.dstOff, Wg2.rawRow, Wg2.numGroups,
    Wg2.topkBlock, Wg2.rowInAtom]
  omega

/-- The observed raw word and scale supply exactly this BF16 byte of the MMA input tile. -/
theorem dequantized_payload_byte {row : Nat → Nat} {L : Launch} {g s word sc : Nat}
    (hw : ∀ i < Wg2.rawBytesPerThread, Wg2.Numeric.byteAt word i = row (Wg2.elemByte L g s i))
    (hs : Wg2.Numeric.byteAt sc (Wg2.scaleIdx L g s) = row (512 + Wg2.scaleIdx L g s))
    (elem : Fin 8) (byte : Fin 2) :
    (Wg2.Numeric.dequantChunk word
      (Wg2.Numeric.byteAt sc (Wg2.scaleIdx L g s))).toBytes[2 * elem.val + byte.val]? =
      some (.float .bf16 (dequant row (Wg2.logicalElem L g s elem.val)), byte.val) := by
  rw [Wg2.chunkBytes_eq_row L g s row hw hs]
  fin_cases elem <;> fin_cases byte <;> rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
