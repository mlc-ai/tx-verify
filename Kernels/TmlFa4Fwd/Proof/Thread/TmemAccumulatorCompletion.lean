-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorSources
public import Lemmas.Tcgen05.TcMmaSource
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreCommitActors
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityScore
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private structure AccumulatorLayout (l : Launch) (i : EvId) (d : Nat)
    (op : OperandSpec) (mask : List Nat) : Prop where
  aligned : d % 128 = 0
  bounded : d+128 ≤ 512
  group : op.descriptor.group = .one
  rows : op.descriptor.m = 128
  columns : op.descriptor.n = 128
  valid : Valid op.descriptor
  low : op.lowCta = i.1/l.block
  high : op.highCta = i.1/l.block
  unmasked : mask = List.replicate 4 0

private theorem accumulatorLayout {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d op acc mask) : AccumulatorLayout l i d op mask := by
  rcases actualMmaInstruction hX hi with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
  · have hDest := hQk.scoreDestination hp hX
    have hOp := hQk.queryOperand hp hX
    refine ⟨?_,?_,?_,?_,?_,?_,hOp.ctaLow,hOp.ctaHigh,(hQk.issueFlags hX).2⟩
    · rw [hDest,scoreColumn]
      omega
    · exact hDest.symm ▸ (scoreColumn_range (qkStage block)).trans (by decide)
    all_goals rw [hOp.descriptor]; decide
  · have hDest := hPv.outputDestination hp hX
    obtain ⟨_,_,hDesc,hLo,hHi⟩ := hPv.valueOperand hp hX
    refine ⟨?_,?_,?_,?_,?_,?_,hLo,hHi,(hPv.fixedOperandFields hX).2.2⟩
    · rw [hDest,outputColumn]
      omega
    · exact hDest.symm ▸ outputColumn_range (pvSite block).stage
    all_goals rw [hDesc]; decide

private theorem AccumulatorLayout.result {l : Launch} {i : EvId} {d : Nat}
    {op : OperandSpec} {mask : List Nat} (h : AccumulatorLayout l i d op mask)
    (row col : Nat) : resultCell op d row col =
      if row < 128 ∧ col < 128 then some ⟨i.1/l.block,row,d+col⟩ else none := by
  rw [resultCell_layoutD h.group h.rows h.valid,h.columns,h.low]
  simp [h.bounded]

private theorem AccumulatorLayout.write {l : Launch} {i : EvId} {d : Nat}
    {op : OperandSpec} {mask : List Nat} (h : AccumulatorLayout l i d op mask)
    (row col : Nat) : writeCell op d mask row col =
      if row < 128 ∧ col < 128 then some ⟨i.1/l.block,row,d+col⟩ else none := by
  by_cases hFit : row < 128 ∧ col < 128
  · rw [ite_eq_left hFit,h.unmasked]
    apply writeCell_no_mask_128 h.group h.rows hFit.1 hFit.1
    rw [h.result,ite_eq_left hFit]
  rw [ite_eq_right hFit]
  cases hw : writeCell op d mask row col with
  | none => rfl
  | some c =>
    have hC := writeCell_resultCell hw
    rw [h.result,ite_eq_right hFit] at hC
    cases hC

/-- An MMA accumulator source is an earlier same-thread issue whose identical
D footprint must already be completed when the reading MMA completes. -/
theorem mmaAccumulatorMmaSourceDone {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hGuard : SyncGuarded l kernel X)
    {writer reader : EvId} {cell : Cell} (hSource : ReadSource l X .acc writer reader cell)
    (hRead : X.MmaReadCell reader cell) (hWritten : X.MmaCell writer cell)
    (hDone : X.async.mmaDone reader = true) :
    writer.1 = reader.1 ∧ writer.2 < reader.2 ∧ X.async.mmaDone writer = true := by
  obtain ⟨d,op,mask,row,col,hI,hR⟩ := hRead
  obtain ⟨d',op',acc',mask',row',col',hW,hWrite⟩ := hWritten
  have hA := accumulatorLayout hp hX hI
  have hB := accumulatorLayout hp hX hW
  rw [hA.result] at hR
  have hNonempty := hWrite
  rw [hB.write] at hWrite
  have hRa : row < 128 ∧ col < 128 := by
    by_contra h
    rw [ite_eq_right h] at hR
    cases hR
  have hRb : row' < 128 ∧ col' < 128 := by
    by_contra h
    rw [ite_eq_right h] at hWrite
    cases hWrite
  rw [ite_eq_left hRa] at hR
  rw [ite_eq_left hRb] at hWrite
  have hSame := Option.some.inj (hWrite.trans hR.symm)
  have hCta : writer.1/l.block = reader.1/l.block := congrArg Cell.cta hSame
  have hD : d' = d := by
    have hCol := congrArg Cell.column hSame
    dsimp only at hCol
    have hM := hA.aligned
    have hM' := hB.aligned
    omega
  have hLane := mmaIssueSameThread hp hX hW hI hCta
  obtain ⟨tag,he⟩ := hI
  obtain ⟨tag',hf⟩ := hW
  have hEarlier := tcStep_same_thread (tcStep_acyclic hX hGuard) hSource.2.2.1.tcStep
    hLane (by rw [he]; rfl)
  have hWp : SameWarp l writer.1 reader.1 :=
    ⟨⟨event_thread_lt hX hf,event_thread_lt hX he,hCta⟩,by rw [hLane]⟩
  have hSameD : SameAccumulator d' op' d op := ⟨hD,hB.rows.trans hA.rows.symm,
    hB.columns.trans hA.columns.symm,hB.low.trans (hCta.trans hA.low.symm),
    hB.high.trans (hCta.trans hA.high.symm)⟩
  have hP := po_of_not_access hLane hEarlier (len_of_get he) (by rw [he]; rfl)
  have hPipe : Pipelined l X .dWrite writer .dWrite reader :=
    ⟨hWp,.inl (.single (.inl hP)),d',op',acc',mask',d,op,true,mask,⟨tag',hf⟩,⟨tag,he⟩,hSameD⟩
  have hFoot : SameWrites X writer reader := by
    refine ⟨d',op',acc',mask',d,op,true,mask,⟨tag',hf⟩,⟨tag,he⟩,?_,row',col',cell,hNonempty⟩
    intro row col
    rw [hB.write,hA.write,hCta,hD]
  exact ⟨hLane,hEarlier,hX.mmaCompletion writer reader ⟨hLane,hEarlier,hPipe,hFoot⟩ hDone⟩

/-- All actual MMA instructions use the same BF16/FP32 arithmetic mode. -/
theorem mmaBf16Arithmetic {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d op acc mask) : op.descriptor.kind = .f16 .bf16 .f32 ∧
      op.descriptor.ws = false ∧ op.descriptor.negateA = false ∧
      op.descriptor.negateB = false := by
  rcases actualMmaInstruction hX hi with ⟨_,_,hQk⟩ | ⟨_,_,hPv⟩
  · rw [(hQk.queryOperand hp hX).descriptor]
    decide
  · obtain ⟨_,_,hDesc,_⟩ := hPv.valueOperand hp hX
    rw [hDesc]
    decide

/-- Completed MMAs have their actual recorded operand arrays with the required lengths. -/
theorem mmaCompletedOperandRecord {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d op acc mask) (hDone : X.async.mmaDone i = true) :
    ∃ ops, X.async.mmaOperands i = some ops ∧ Valid op.descriptor ∧
      ops.a.length = Operand.bytes .a op.descriptor ∧
      ops.b.length = Operand.bytes .b op.descriptor := by
  rcases hX.tma.2.1.1 i (hX.tma.2.1.2 i hDone) with
    ⟨_,_,_,_,ops,hOther,hOps,hValid,hLenA,hLenB⟩ | ⟨_,_,hCopy,_⟩ | ⟨_,_,hShift,_⟩
  · obtain ⟨_,rfl,_,_⟩ := mmaIssue_params hOther hi
    exact ⟨ops,hOps,hValid,hLenA,hLenB⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim

/-- A score commit on the elected issuer is a different event from its MMA. -/
theorem scoreCommitIndexNeMma {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit i : EvId} {cta d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : Scores.ScoreCommit l X commit cta stage spec rank)
    (hi : X.MmaIssue i d op acc mask) (hCta : i.1/l.block = cta) :
    commit.2 ≠ i.2 := by
  intro hIndex
  have hLane := Scores.mmaAndScoreCommitSameThread hp hX hi hCommit hCta
  obtain ⟨_,he⟩ := hi
  obtain ⟨_,hf⟩ := hCommit.1
  rw [Prod.ext hLane.symm hIndex,he] at hf
  cases congrArg Event.kind (Option.some.inj hf)

/-- The same trace event cannot issue both an MMA and an ordinary Tensor Memory store. -/
theorem mmaIssueNeStore {l : Launch} {X : Execution} {st mma : EvId} {d : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hi : X.MmaIssue mma d op acc mask) (hs : StoreCell l X st cell) : mma ≠ st := by
  rintro rfl
  obtain ⟨_,he⟩ := hi
  obtain ⟨_,_,_,_,⟨_,hf⟩,_,_⟩ := hs
  rw [he] at hf
  cases congrArg Event.kind (Option.some.inj hf)

end PTX.Kernels.TmlFa4Fwd.Thread
