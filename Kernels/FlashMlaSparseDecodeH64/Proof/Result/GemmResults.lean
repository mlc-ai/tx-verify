-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmValues

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
open MmaDataTrace Wg1Mma

noncomputable section

/-- Zero lane masks leave every represented result enabled in the single-CTA head64 tile. -/
theorem writeCell_zeroMask {s : TcMma.OperandSpec} {base row col : Nat}
    {cell : TcMma.Cell} (hg : s.descriptor.group = .one) (hm : s.descriptor.m = 64)
    (hr : row < 64) (hl : cell.lane < 128)
    (hc : TcMma.resultCell s base row col = some cell) :
    TcMma.writeCell s base [0, 0, 0, 0] row col = some cell := by
  have hv : TcMma.OutputMaskValid s.descriptor.group [0, 0, 0, 0] := by
    rw [hg]
    decide
  have hrow : row / (s.descriptor.m / s.descriptor.group.size) = 0 := by
    rw [hm, hg]
    exact Nat.div_eq_of_lt hr
  have hword : ([0, 0, 0, 0] : List Nat)[cell.lane / 32]? = some 0 := by
    have he : cell.lane / 32 < 4 := by omega
    interval_cases cell.lane / 32 <;> rfl
  simp only [TcMma.writeCell, hv, not_true_eq_false, ite_false, hc, hrow, Nat.zero_mul,
    Nat.zero_add, bind, Option.bind, hword, Nat.zero_div, Nat.zero_mod, ite_true]

/-- Every output lane of a QK issue is enabled, and writes its token/half cell. -/
theorem qkWriteCell (L : Launch) (g i : Nat) (issue : Fin 16) (row : Fin 64) (col : Fin 128) :
    TcMma.writeCell (qkOperands L g i issue) tmemP [0, 0, 0, 0] row.val col.val =
      some ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ := by
  refine writeCell_zeroMask (s := qkOperands L g i issue) rfl rfl row.isLt ?_
    (qkResultCell L g i issue row col)
  dsimp only
  omega

/-- Every output lane of a PV issue is enabled, and writes its position in O. -/
theorem pvWriteCell (L : Launch) (g i : Nat) (issue : Fin 8) (row : Fin 64) (col : Fin 256) :
    TcMma.writeCell (pvOperands L g i issue) (pvDest issue) [0, 0, 0, 0] row.val col.val =
      some ⟨ctaOf L g, row.val + 64 * (col.val / 128), pvDest issue + col.val % 128⟩ := by
  refine writeCell_zeroMask (s := pvOperands L g i issue) rfl rfl row.isLt ?_
    (pvResultCell L g i issue row col)
  dsimp only
  omega

/-- The previous F32 value of this cell, obtained from the actual accumulating read when enabled.
On an overwrite there is no accumulator read. -/
inductive GemmAccumulator (L : Launch) (X : Execution) (event : EvId) (cell : TcMma.Cell) :
    Bool → ℝ → Prop
  | overwrite : GemmAccumulator L X event cell false 0
  | priorMma {source : EvId} {v : ℝ}
      (read : TcMma.ReadSource L X .acc source event cell)
      (value : TcMma.Result L Assumptions.all X source cell (.float .f32 v)) :
      GemmAccumulator L X event cell true v
  | priorStore {source : EvId} {v : ℝ}
      (read : TcMma.ReadSource L X .acc source event cell)
      (value : TcMma.StoreValue L X source cell (.float .f32 v)) :
      GemmAccumulator L X event cell true v

/-- An issue with observed operands writes its dot product and, when enabled, the actual previous
value of the same cell. -/
theorem gemm_result_of_eval {L : Launch} {X : Execution} {event : EvId} {base : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {operands : AsyncCopy.MmaOperands}
    (hi : X.MmaIssue event base s acc mask) (hr : X.async.mmaOperands event = some operands)
    {row col : Nat} {cell : TcMma.Cell} {prev dot : ℝ}
    (hc : TcMma.writeCell s base mask row col = some cell)
    (hp : GemmAccumulator L X event cell acc prev)
    (he : ∀ old, Assumption.idealMmaAccumulator .f32 acc old = .ok prev →
      TcMma.eval Assumptions.all s.descriptor acc operands.a operands.b old row col =
        .ok (.float .f32 (dot + prev))) :
    TcMma.Result L Assumptions.all X event cell (.float .f32 (dot + prev)) := by
  cases hp with
  | overwrite => exact .overwrite hi hc hr (he none rfl)
  | priorMma hread hvalue => exact .accumulate hi hc hr hvalue hread (he _ (by
      simp [Assumption.idealMmaAccumulator, valFloat, pure, Except.pure]))
  | priorStore hread hvalue => exact .accumulateStored hi hc hr hvalue hread (he _ (by
      simp [Assumption.idealMmaAccumulator, valFloat, pure, Except.pure]))

/-- A QK chunk leaves its computed F32 sum in the addressed score cell. -/
theorem qk_chunk_result {P : Params} {L : Launch} {g block : Nat} {X : Execution}
    {event : EvId} {issue : Fin 16} {operands : AsyncCopy.MmaOperands}
    (ht : AsyncCopy.TcEffectsOk X)
    (hi : X.MmaIssue event tmemP (qkOperands L g block issue) (qkAccum issue) [0, 0, 0, 0])
    (hr : X.async.mmaOperands event = some operands)
    (row : Fin 64) (col : Fin 128) (key : Nat → ℝ)
    (ha : Bf16Operand operands.a (row.val + 64 * (col.val / 64)) fun k =>
      P.q (batchOf L g) (queryOf L g) row.val
        (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k))
    (hb : Bf16Operand operands.b col.val fun k =>
      key (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k))
    {prev : ℝ}
    (hp : GemmAccumulator L X event
      ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩ (qkAccum issue) prev) :
    TcMma.Result L Assumptions.all X event
      ⟨ctaOf L g, row.val + 64 * (col.val / 64), tmemP + col.val % 64⟩
      (.float .f32 ((∑ k ∈ Finset.range 16,
        P.q (batchOf L g) (queryOf L g) row.val
          (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k) *
        key (128 * (issue.val / 4) + 64 * (col.val / 64) + 16 * (issue.val % 4) + k)) + prev)) := by
  refine gemm_result_of_eval hi hr (qkWriteCell L g block issue row col) hp ?_
  intro _ hold
  exact qk_eval_chunk ht hi hr row col _ key ha hb hold

/-- A PV chunk leaves its F32 weighted-value sum in the addressed output cell. -/
theorem pv_chunk_result {L : Launch} {g block : Nat} {X : Execution} {event : EvId}
    {issue : Fin 8} {operands : AsyncCopy.MmaOperands}
    (ht : AsyncCopy.TcEffectsOk X)
    (hi : X.MmaIssue event (pvDest issue) (pvOperands L g block issue) (pvAccum block issue)
      [0, 0, 0, 0])
    (hr : X.async.mmaOperands event = some operands)
    (row : Fin 64) (col : Fin 256) (weight : Nat → ℝ) (value : Nat → Nat → ℝ)
    (ha : Bf16Operand operands.a (row.val + 64 * (col.val / 128)) fun k =>
      weight (16 * (issue.val / 2) + k))
    (hb : Bf16Operand operands.b col.val fun k =>
      value (16 * (issue.val / 2) + k) (pvFeature issue col))
    {prev : ℝ}
    (hp : GemmAccumulator L X event
      ⟨ctaOf L g, row.val + 64 * (col.val / 128), pvDest issue + col.val % 128⟩
      (pvAccum block issue) prev) :
    TcMma.Result L Assumptions.all X event
      ⟨ctaOf L g, row.val + 64 * (col.val / 128), pvDest issue + col.val % 128⟩
      (.float .f32 ((∑ k ∈ Finset.range 16,
        weight (16 * (issue.val / 2) + k) *
          value (16 * (issue.val / 2) + k) (pvFeature issue col)) + prev)) := by
  refine gemm_result_of_eval hi hr (pvWriteCell L g block issue row col) hp ?_
  intro _ hold
  exact pv_eval_chunk ht hi hr row col weight value ha hb hold

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
