-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccumulatorProvenance
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.MmaBf16Eval
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma PTX.AsyncCopy Thread

/-- All recorded operands used by an actual completed MMA cell denote BF16 reals. -/
def CompletedMmaOperandsAreBf16 (X : Execution) : Prop :=
  ∀ i cell d spec acc mask row col (ops : MmaOperands),
    X.MmaIssue i d spec acc mask → X.async.mmaDone i = true →
    writeCell spec d mask row col = some cell → X.async.mmaOperands i = some ops →
    (∀ k < 16, ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x) ∧
    (∀ k < 16, ∃ y, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok y)

/-- An ordinary store selected as an accumulator source leaves an FP32 real. -/
def StoredAccumulatorIsF32 (l : Launch) (X : Execution) : Prop :=
  ∀ source reader cell value, X.MmaReadCell reader cell →
    ReadSource l X .acc source reader cell → StoreValue l X source cell value →
    ∃ r, value = .float .f32 r

private theorem valueOfStoreCell {l : Launch} {X : Execution} {i : EvId} {cell : Cell}
    (h : StoreCell l X i cell) : ∃ v, StoreValue l X i cell v := by
  obtain ⟨addr,vals,shape,j,hStore,hJ,hCell⟩ := h
  exact ⟨vals[j],addr,vals,shape,j,hStore,List.getElem?_eq_some_iff.mpr ⟨hJ,rfl⟩,hCell⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    (hOperands : CompletedMmaOperandsAreBf16 X)
include hp hX hCuQ hOperands

/-- An issued MMA result only depends on operand bytes and earlier accumulator writers. -/
theorem mmaCompletedResultOfEarlierValues {i : EvId} {cell : Cell}
    (hDone : X.async.mmaDone i = true) (hCell : X.MmaCell i cell)
    (hEarlierMma : ∀ source, Relation.TransGen (TcStep l X) source i →
      source.2 < i.2 → X.async.mmaDone source = true → X.MmaCell source cell →
      ∃ r, Result l Assumptions.all X source cell (.float .f32 r))
    (hEarlierStore : ∀ source, Relation.TransGen (TcStep l X) source i →
      ∀ {value}, X.MmaReadCell i cell → ReadSource l X .acc source i cell →
      StoreValue l X source cell value → ∃ r, value = .float .f32 r) :
    ∃ r, Result l Assumptions.all X i cell (.float .f32 r) := by
  classical
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  obtain ⟨d,op,acc,mask,row,col,hIssue,hWrite⟩ := hCell
  obtain ⟨ops,hOps,hValid,hA,hB⟩ := mmaCompletedOperandRecord hX hIssue hDone
  obtain ⟨hKind,hWs,hNegA,hNegB⟩ := mmaBf16Arithmetic hp hX hIssue
  obtain ⟨hRow,hCol⟩ := resultCell_rowcol (writeCell_resultCell hWrite)
  obtain ⟨hElemsA,hElemsB⟩ :=
    hOperands i cell d op acc mask row col ops hIssue hDone hWrite hOps
  choose x hx using hElemsA
  choose y hy using hElemsB
  let a (k : Nat) := if kBound : k < 16 then x k kBound else 0
  let b (k : Nat) := if kBound : k < 16 then y k kBound else 0
  have hAElem : ∀ k < 16,
      Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok (a k) := by
    intro k hk
    simpa only [a,dite_eq_left hk] using hx k hk
  have hBElem : ∀ k < 16,
      Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b col k = .ok (b k) := by
    intro k hk
    simpa only [b,dite_eq_left hk] using hy k hk
  have hEval {enabled : Bool} {old : Option Value} {r : ℝ}
      (hOld : Assumption.idealMmaAccumulator .f32 enabled old = .ok r) :
      ∃ z, eval Assumptions.all op.descriptor enabled ops.a ops.b old row col =
        .ok (.float .f32 z) :=
    ⟨_,Mma.evalBf16Cell hKind hValid hWs hNegA hNegB hA hB hRow hCol hAElem hBElem hOld⟩
  cases acc with
  | false =>
    obtain ⟨r,hr⟩ := hEval (enabled := false) (old := none) (r := 0) rfl
    exact ⟨r,.overwrite hIssue hWrite hOps hr⟩
  | true =>
    have hRead : X.MmaReadCell i cell :=
      ⟨d,op,mask,row,col,hIssue,writeCell_resultCell hWrite⟩
    obtain ⟨source,hSource⟩ := mmaAccumulatorReadSource hp hX hCuQ hRead
    rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · obtain ⟨_,hEarlier,hEarlierDone⟩ :=
        mmaAccumulatorMmaSourceDone hp hX hGuard hSource hRead hMma hDone
      obtain ⟨r,hPrev⟩ := hEarlierMma source hSource.2.2.1.tcStep hEarlier hEarlierDone hMma
      obtain ⟨z,hz⟩ := hEval (enabled := true) (old := some (.float .f32 r)) (r := r) rfl
      exact ⟨z,.accumulate hIssue hWrite hOps hPrev hSource hz⟩
    · obtain ⟨old,hOld⟩ := valueOfStoreCell hStore
      obtain ⟨r,rfl⟩ := hEarlierStore source hSource.2.2.1.tcStep hRead hSource hOld
      obtain ⟨z,hz⟩ := hEval (enabled := true) (old := some (.float .f32 r)) (r := r) rfl
      exact ⟨z,.accumulateStored hIssue hWrite hOps hOld hSource hz⟩
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim

/-- A completed result is derived from the real recorded A and B operands and
the current or carried accumulator's stable source. -/
theorem mmaCompletedResultOfOperands (hStored : StoredAccumulatorIsF32 l X) {i : EvId} {cell : Cell}
    (hDone : X.async.mmaDone i = true) (hCell : X.MmaCell i cell) :
    ∃ r, Result l Assumptions.all X i cell (.float .f32 r) := by
  classical
  have results (n : Nat) :
      ∀ i : EvId, i.2 = n → X.async.mmaDone i = true → ∀ cell, X.MmaCell i cell →
        ∃ r, Result l Assumptions.all X i cell (.float .f32 r) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hIndex hDone cell hCell
      apply mmaCompletedResultOfEarlierValues hp hX hCuQ hOperands hDone hCell
      · intro source _ hEarlier hEarlierDone hMma
        exact ih source.2 (hIndex ▸ hEarlier) source rfl hEarlierDone cell hMma
      · intro source _ v hRead hSource hOld
        exact hStored source i cell v hRead hSource hOld
  exact results i.2 i rfl hDone cell hCell

/-- The remaining numerical premises for the completed-MMA instruction check. -/
theorem mmaCompletedValuesOfOperands (hStored : StoredAccumulatorIsF32 l X) (i : EvId)
    : CompletedValues l Assumptions.all X i := by
  intro hDone cell hCell
  obtain ⟨r,hr⟩ := mmaCompletedResultOfOperands hp hX hCuQ hOperands hStored hDone hCell
  exact ⟨.float .f32 r,hr⟩

/-- A completed C read has a stable writer and the value that writer produced. -/
theorem mmaAccumulatorValuesOfOperands (hStored : StoredAccumulatorIsF32 l X) {i : EvId}
    {cell : Cell} (hDone : X.async.mmaDone i = true) (hRead : X.MmaReadCell i cell) :
    ∃ source value, ReadSource l X .acc source i cell ∧
      Wrote l Assumptions.all X source cell value := by
  obtain ⟨source,hSource⟩ := mmaAccumulatorReadSource hp hX hCuQ hRead
  rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
  · have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
    have hEarlier := (mmaAccumulatorMmaSourceDone hp hX hGuard hSource hRead hMma hDone).2.2
    obtain ⟨r,hr⟩ := mmaCompletedResultOfOperands hp hX hCuQ hOperands hStored hEarlier hMma
    exact ⟨source,.float .f32 r,hSource,.inl hr⟩
  · obtain ⟨v,hV⟩ := valueOfStoreCell hStore
    exact ⟨source,v,hSource,.inr (.inl hV)⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
