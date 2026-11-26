-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaResults
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.SourceDone
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # The value of an MMA result: the sixteen products and the old value

`mma_result_sum`: a done MMA's result at a cell (`TcMma.Result`) is the single-precision number
`Σ_{k<16} x_k y_k + prev` (the ideal arithmetic is exact: no rounding), where `x_k` is the
element `k` of the A row of the output (`operandRow`) and `y_k` that of the B column, as the
operand bytes decode (`MmaElements`), and `prev` is `0` (no accumulation) or the number the
accumulator source's word reads as: an MMA result or a store. The QK chain's score and the
operand elements' bytes are built on it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

namespace TmRace

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The value of a result**: the sixteen products of the decoded operand elements plus the
number the accumulator source's word reads as (`0` for an overwrite). -/
theorem mma_result_sum (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hT : TmemRows P L X) (hO : MmaOne L X) (hG : SyncGuarded L kernel X)
    {i : EvId} (hE : MmaElemAt X i) {cell : TcMma.Cell} {v : Value}
    (hold : ∀ src old, Relation.TransGen (TcMma.TcStep L X) src i →
      ((X.async.mmaDone src = true ∧ TcMma.Result L Assumptions.all X src cell old) ∨
        TcMma.StoreValue L X src cell old) → ∃ r : ℝ, valFloat .f32 old = .ok r)
    (hd : X.async.mmaDone i = true) (hr : TcMma.Result L Assumptions.all X i cell v) :
    ∃ (d : Nat) (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (row col : Nat)
      (ops : AsyncCopy.MmaOperands) (x y : Nat → ℝ) (prev : ℝ),
      X.MmaIssue i d s acc mask ∧ TcMma.writeCell s d mask row col = some cell ∧
      X.async.mmaOperands i = some ops ∧
      (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
        (TcMma.operandRow s.descriptor row col) k = .ok (x k)) ∧
      (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok (y k)) ∧
      v = .float .f32 ((∑ k ∈ Finset.range 16, x k * y k) + prev) ∧
      ((acc = false ∧ prev = 0) ∨ (acc = true ∧ ∃ src old,
        TcMma.ReadSource L X .acc src i cell ∧
          (TcMma.Result L Assumptions.all X src cell old ∨ TcMma.StoreValue L X src cell old) ∧
          valFloat .f32 old = .ok prev)) := by
  have key : ∀ {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat} {row col : Nat}
      {ops : AsyncCopy.MmaOperands} {old : Option Value} {prev : ℝ},
      X.MmaIssue i d s acc mask → TcMma.writeCell s d mask row col = some cell →
      X.async.mmaOperands i = some ops →
      Assumption.idealMmaAccumulator .f32 acc old = .ok prev →
      TcMma.eval Assumptions.all s.descriptor acc ops.a ops.b old row col = .ok v →
      ∃ x y : Nat → ℝ,
        (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a
          (TcMma.operandRow s.descriptor row col) k = .ok (x k)) ∧
        (∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok (y k)) ∧
        v = .float .f32 ((∑ k ∈ Finset.range 16, x k * y k) + prev) := by
    intro d s acc mask row col ops old prev hi hpos hops hprev heq
    obtain ⟨hv, hla, hlb⟩ := hX.mma_observation_shape hi hops
    obtain ⟨pc, he⟩ := id hi
    have hc : TcMma.TmemWrite L X i cell := .inl ⟨d, s, acc, mask, row, col, hi, hpos⟩
    obtain ⟨-, -, -, aT, idc, hcol, hmo⟩ := mma_class hp hX hT he hc
    obtain ⟨hk, hna, hnb⟩ : s.descriptor.kind = .f16 .bf16 .f32 ∧ s.descriptor.negateA = false ∧
        s.descriptor.negateB = false := by
      obtain ⟨-, hdec, -⟩ := hmo
      refine desc_bf16 ?_ hdec
      rcases hcol with ⟨h1, -⟩ | ⟨h1, -⟩
      exacts [.inl h1, .inr h1]
    obtain ⟨hrow, hcl⟩ := TcMma.resultCell_rowcol (TcMma.writeCell_resultCell hpos)
    obtain ⟨hAe, hBe⟩ := hE d s acc mask ops row col cell hi hd hops hpos
    choose! x hx using hAe
    choose! y hy using hBe
    have hsum := Result.bf16Mma_sum hk hv hna hnb (by rw [hla]; simp [TcMma.Operand.bytes,
      TcMma.Operand.rows, TcMma.Operand.extent]) (by rw [hlb]; simp [TcMma.Operand.bytes,
      TcMma.Operand.rows, TcMma.Operand.extent]) hrow hcl hx hy hprev
    rw [hsum] at heq
    exact ⟨x, y, hx, hy, (Except.ok.inj heq).symm⟩
  cases hr with
  | overwrite hi hpos hops harith =>
    obtain ⟨x, y, hx, hy, hv⟩ := key hi hpos hops (old := none) (prev := 0) rfl harith
    exact ⟨_, _, _, _, _, _, _, x, y, 0, hi, hpos, hops, hx, hy, hv, .inl ⟨rfl, rfl⟩⟩
  | @accumulate _ _ _ _ row col _ _ _ source _ hi hpos hops hprev hprov harith =>
    have hmc : X.MmaCell source cell := by
      cases hprev with
      | overwrite hi' hp' _ _ => exact ⟨_, _, _, _, _, _, hi', hp'⟩
      | accumulate hi' hp' _ _ _ _ => exact ⟨_, _, _, _, _, _, hi', hp'⟩
      | accumulateStored hi' hp' _ _ _ _ => exact ⟨_, _, _, _, _, _, hi', hp'⟩
    have hdK := acc_mma_done hp hX hT hO hG hd ⟨_, _, _, row, col, hi,
      TcMma.writeCell_resultCell hpos⟩ hprov hmc
    obtain ⟨r, hrr⟩ := hold _ _ hprov.2.2.1.tcStep (.inl ⟨hdK, hprev⟩)
    obtain ⟨x, y, hx, hy, hv⟩ := key hi hpos hops (old := some _) (prev := r)
      (by simp [Assumption.idealMmaAccumulator, hrr]) harith
    exact ⟨_, _, _, _, _, _, _, x, y, r, hi, hpos, hops, hx, hy, hv,
      .inr ⟨rfl, _, _, hprov, .inl hprev, hrr⟩⟩
  | accumulateStored hi hpos hops hprev hprov harith =>
    obtain ⟨r, hrr⟩ := hold _ _ hprov.2.2.1.tcStep (.inr hprev)
    obtain ⟨x, y, hx, hy, hv⟩ := key hi hpos hops (old := some _) (prev := r)
      (by simp [Assumption.idealMmaAccumulator, hrr]) harith
    exact ⟨_, _, _, _, _, _, _, x, y, r, hi, hpos, hops, hx, hy, hv,
      .inr ⟨rfl, _, _, hprov, .inr hprev, hrr⟩⟩

end TmRace
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
