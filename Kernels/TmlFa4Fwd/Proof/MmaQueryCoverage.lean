-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionSource
public import Kernels.TmlFa4Fwd.Proof.MmaQkInputLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX Correction Epilogue

/-- The two planes of each Q stage occupy the four output subboxes of correction stage zero. -/
def correctionQueryStage (subbox : Fin 4) : Fin 2 :=
  ⟨subbox.val / 2, by have := subbox.isLt; omega⟩

/-- Each score fragment reads 32 bytes of a row. An output element covers four row bytes. -/
def correctionQueryFragment (subbox : Fin 4) (x offset : Nat) (hx : x < 32)
    (hb : offset < 4) : Fin 8 :=
  ⟨4 * (subbox.val % 2) + (4 * x + offset) / 32, by omega⟩

/-- The byte's operand ordinal within that score fragment. -/
def correctionQueryByte (x row offset : Nat) : Nat :=
  32 * row + (4 * x + offset) % 32

/-- At an issued QK fragment the fields of operand A are independent of the K-ring state. -/
structure QueryOperandFragment (l : Launch) (g : Nat) (stage : Fin 2) (step : Fin 8)
    (op : TcMma.OperandSpec) : Prop where
  descriptor : op.descriptor = qkDescriptor
  address : op.a = sharedDescriptor (qStart l stage + qkFragment step) 16
  ctaLow : op.lowCta = g / l.block
  ctaHigh : op.highCta = g / l.block
  shared : op.aTmem = none

private theorem queryFragmentLocation {l : Launch} {g : Nat} {stage : Fin 2} {step : Fin 8}
    {op : TcMma.OperandSpec} (hOp : QueryOperandFragment l g stage step op)
    {row k b : Nat} (hr : row < 128) (hk : k < 16) (hb : b < 2) :
    op.byteLoc .a (qkByteIndex row k b) = some ⟨.shared, g / l.block,
      TensorSwizzle.offset .b128 0 (qStart l stage + qkFragment step + 128 * row + 2 * k + b)⟩ := by
  let block : Fin 4 := ⟨stage.val, by have := stage.isLt; omega⟩
  have hStage : qkStage block = stage := Fin.ext (Nat.mod_eq_of_lt stage.isLt)
  have hByte := qkInputByteLoc l g block step 0 .a hr hk hb
  have hSame : op.byteLoc .a (qkByteIndex row k b) =
      (qkOperands l g block step 0).byteLoc .a (qkByteIndex row k b) := by
    simp only [TcMma.OperandSpec.byteLoc, hOp.descriptor, hOp.address, hOp.ctaLow, hOp.ctaHigh,
      hOp.shared, qkOperands, hStage]
  exact hSame.trans (by simpa only [qkInputStart, hStage] using hByte)

/-- Any byte covered by a stage-zero correction element is an A byte of its designated QK
fragment, independently of arithmetic values, transaction completion or warp exit. -/
theorem correctionQueryByteLoc {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {mma writer x row offset : Nat} {subbox : Fin 4} {op : TcMma.OperandSpec}
    (hCta : mma / l.block = writer / l.block) (hx : x < 32) (hy : row < 128) (hb : offset < 4)
    (hOperand : QueryOperandFragment l mma (correctionQueryStage subbox)
      (correctionQueryFragment subbox x offset hx hb) op) :
    op.byteLoc .a (correctionQueryByte x row offset) =
      some ((outputElementAccess l writer 0 subbox x row).loc.at offset) := by
  let q := 4 * x + offset
  let k := (q % 32) / 2
  let b := q % 2
  have hK : k < 16 := by dsimp [k]; omega
  have hB : b < 2 := by dsimp [b]; omega
  have hIndex : qkByteIndex row k b = correctionQueryByte x row offset := by
    dsimp [qkByteIndex, correctionQueryByte, k, b, q]; omega
  let base := (sharedSlot l writer 0 subbox).addr
  have hFragment : qStart l (correctionQueryStage subbox) +
        qkFragment (correctionQueryFragment subbox x offset hx hb) = base + 32 * (q / 32) := by
    have hSub := subbox.isLt
    change l.sharedBase + 3072 + 32768 * (subbox.val / 2) +
      (32 * ((4 * (subbox.val % 2) + q / 32) % 4) +
        16384 * ((4 * (subbox.val % 2) + q / 32) / 4)) = _
    simp only [base, sharedSlot, Fin.val_zero, Nat.mul_zero]
    have hQ : q < 128 := by dsimp [q]; omega
    omega
  have hLinear : base + 32 * (q / 32) + 128 * row + 2 * k + b =
      base + (128 * row + 16 * (x / 4) + (4 * (x % 4) + offset)) := by
    dsimp [q, k, b]; omega
  have hChunk : x / 4 < 8 := by omega
  have hWithin : 4 * (x % 4) + offset < 16 := by omega
  have hLoc := queryFragmentLocation hOperand hy hK hB
  rw [hIndex, hFragment, hLinear, hCta, outputChunk_swizzle hp writer 0 subbox hChunk hWithin]
    at hLoc
  simpa only [outputElementAccess, outputChunkLoc, sharedSlot, Loc.at, Nat.add_assoc] using hLoc

end PTX.Kernels.TmlFa4Fwd.Mma
