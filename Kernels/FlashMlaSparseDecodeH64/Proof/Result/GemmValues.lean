-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Gemm
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaDataTrace
public import Lemmas.Tcgen05.MmaOperandObservations
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open PTX MmaDataTrace

noncomputable section

/-- A row of the operand snapshot holds the exact two BF16 bytes of each contraction value. -/
def Bf16Operand (bytes : List (Option Byte)) (row : Nat) (value : Nat → ℝ) : Prop :=
  ∀ k < 16, ∀ b < 2, bytes[2 * (row * 16 + k) + b]? =
    some (some (.float .bf16 (value k), b))

theorem Bf16Operand.element {bytes : List (Option Byte)} {row k : Nat} {x : Nat → ℝ}
    {op : TcMma.Operand} (h : Bf16Operand bytes row x) (hk : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) op bytes row k = .ok (x k) := by
  have ha := h k hk 0 (by decide)
  have hb := h k hk 1 (by decide)
  apply bf16MmaElement_of_bytes
  change (bytes.drop (2 * (row * 16 + k))).take 2 =
    [some (.float .bf16 (x k), 0), some (.float .bf16 (x k), 1)]
  simpa only [Nat.add_zero] using TcMma.take_two ha hb

/-- The exact shape of an issued BF16 matrix multiply supplies the lengths used by the
arithmetic interpretation. Its value is the dot product of its observed operands. -/
theorem bf16Mma_eval_observed {X : Execution} {event : EvId} {d : Nat} {s : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (ht : AsyncCopy.TcEffectsOk X) (hi : X.MmaIssue event d s acc mask)
    (hr : X.async.mmaOperands event = some operands)
    (hk : s.descriptor.kind = .f16 .bf16 .f32)
    (hnegA : s.descriptor.negateA = false) (hnegB : s.descriptor.negateB = false)
    {row col : Nat} (hrow : row < s.descriptor.m) (hcol : col < s.descriptor.n)
    {x y : Nat → ℝ} (ha : Bf16Operand operands.a (TcMma.operandRow s.descriptor row col) x)
    (hb : Bf16Operand operands.b col y)
    {old : Option Value} {prev : ℝ}
    (hp : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all s.descriptor acc operands.a operands.b old row col =
      .ok (.float .f32 ((∑ k ∈ Finset.range 16, x k * y k) + prev)) := by
  obtain ⟨hv, ha_len, hb_len⟩ := ht.mma_observation_shape hi hr
  have hla : operands.a.length = TcMma.Operand.bytes .a s.descriptor := by
    simpa only [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, reduceCtorEq,
      true_and] using ha_len
  have hlb : operands.b.length = TcMma.Operand.bytes .b s.descriptor := by
    simpa only [TcMma.Operand.bytes, TcMma.Operand.rows, TcMma.Operand.extent, reduceCtorEq,
      false_and, ite_false] using hb_len
  exact bf16Mma_sum hk hv hnegA hnegB hla hlb hrow hcol
    (fun _ hj => ha.element hj) (fun _ hj => hb.element hj) hp

/-- For a QK issue, the A snapshot row is the head on the datapath half selected by
the key column. The sixteen features are the corresponding slice of the query/key rows. -/
theorem qk_eval_chunk {L : Launch} {g block : Nat} {X : Execution} {event : EvId}
    {issue : Fin 16} {operands : AsyncCopy.MmaOperands}
    (ht : AsyncCopy.TcEffectsOk X)
    (hi : X.MmaIssue event Wg1Mma.tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hr : X.async.mmaOperands event = some operands)
    (row : Fin 64) (col : Fin 128) (query key : Nat → ℝ)
    (ha : Bf16Operand operands.a (row.val + 64 * (col.val / 64)) fun k =>
      query (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k))
    (hb : Bf16Operand operands.b col.val fun k =>
      key (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k))
    {old : Option Value} {prev : ℝ}
    (hp : Assumption.idealMmaAccumulator .f32 (qkAccum issue) old = .ok prev) :
    TcMma.eval Assumptions.all Wg1Mma.qkDescriptor (qkAccum issue)
        operands.a operands.b old row.val col.val =
      .ok (.float .f32 ((∑ k ∈ Finset.range 16,
        query (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k) *
        key (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k)) + prev)) := by
  have he : TcMma.operandRow (qkOperands L g block issue).descriptor row.val col.val =
      row.val + 64 * (col.val / 64) := by
    simp [qkOperands, Wg1Mma.qkDescriptor, TcMma.operandRow, TcMma.columnBlocks, CtaGroup.size]
  rw [← he] at ha
  exact bf16Mma_eval_observed ht hi hr rfl rfl rfl row.isLt col.isLt ha hb hp

/-- For a PV issue, both observed inputs use the same sixteen sparse slots, and
the two output halves are distinguished by their issue and result column. -/
theorem pv_eval_chunk {L : Launch} {g block : Nat} {X : Execution} {event : EvId}
    {issue : Fin 8} {operands : AsyncCopy.MmaOperands}
    (ht : AsyncCopy.TcEffectsOk X)
    (hi : X.MmaIssue event (Wg1Mma.pvDest issue) (pvOperands L g block issue)
      (pvAccum block issue) [0, 0, 0, 0])
    (hr : X.async.mmaOperands event = some operands)
    (row : Fin 64) (col : Fin 256) (weight : Nat → ℝ) (value : Nat → Nat → ℝ)
    (ha : Bf16Operand operands.a (row.val + 64 * (col.val / 128)) fun k =>
      weight (16 * (issue.val / 2) + k))
    (hb : Bf16Operand operands.b col.val fun k =>
      value (16 * (issue.val / 2) + k) (pvFeature issue col))
    {old : Option Value} {prev : ℝ}
    (hp : Assumption.idealMmaAccumulator .f32 (pvAccum block issue) old = .ok prev) :
    TcMma.eval Assumptions.all Wg1Mma.pvDescriptor (pvAccum block issue)
        operands.a operands.b old row.val col.val =
      .ok (.float .f32 ((∑ k ∈ Finset.range 16,
        weight (16 * (issue.val / 2) + k) *
          value (16 * (issue.val / 2) + k) (pvFeature issue col)) + prev)) := by
  have he : TcMma.operandRow (pvOperands L g block issue).descriptor row.val col.val =
      row.val + 64 * (col.val / 128) := by
    simp [pvOperands, Wg1Mma.pvDescriptor, TcMma.operandRow, TcMma.columnBlocks, CtaGroup.size]
  rw [← he] at ha
  exact bf16Mma_eval_observed ht hi hr rfl rfl rfl row.isLt col.isLt ha hb hp

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
