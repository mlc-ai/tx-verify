-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccumulatorProvenance
import Kernels.TmlFa4Fwd.Proof.Thread.TmemAccumulatorCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.TmemInitialScoreStore
import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Order.OrderBaseCausality
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof PTX.TcMma Thread Thread.Scores Protocol.Scores
open PTX.Kernels.TmlFa4Fwd.Mma (qkStage initialQkBlock)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem qkOwnsWrittenCell {i : EvId} {block : Fin 4} {frag : Fin 8} {d row col : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hi : QkInstruction X i block frag d op acc mask) (hCell : resultCell op d row col = some cell)
    : X.MmaCell i cell := by
  have hOperand := hi.queryOperand hp hX
  obtain ⟨hRow,hCol⟩ := resultCell_rowcol hCell
  rw [hOperand.descriptor] at hRow hCol
  have h := writeCell_no_mask_128
    (show op.descriptor.group = .one by rw [hOperand.descriptor]; rfl)
    (show op.descriptor.m = 128 by rw [hOperand.descriptor]; rfl)
    hRow (resultCell_bounds hCell).1 hCell
  rw [← (hi.issueFlags hX).2] at h
  exact ⟨d,op,acc,mask,row,col,⟨_,hi.decoded⟩,h⟩

private theorem mmaCellWriteOrderedAtEarlierIndex (hGuard : SyncGuarded l kernel X) {i j : EvId}
    {cell : Cell} (hi : X.MmaCell i cell) (hj : X.MmaCell j cell) (hBefore : i.2 < j.2) :
    Pipelined l X .dWrite i .dWrite j := by
  have hCta := (mmaWrittenCellCta hp hX hi).symm.trans (mmaWrittenCellCta hp hX hj)
  have ⟨_,_,_,_,_,_,hI,_⟩ := hi
  have ⟨_,_,_,_,_,_,hJ,_⟩ := hj
  have hLane := mmaIssueSameThread hp hX hI hJ hCta
  rcases overlappingMmaOutputPipeline hp hX hi hj (fun h =>
    (Nat.ne_of_lt hBefore) (congrArg Prod.snd h)) with h | h
  · exact h
  · obtain ⟨_,hAt⟩ := hJ
    have hPo := po_of_not_access hLane hBefore (len_of_get hAt) (by rw [hAt]; rfl)
    exact (tcStep_acyclic hX hGuard i
      ((Relation.TransGen.single (.inl (.single (.inl hPo)))).trans h.tcBefore.tcStep)).elim

private theorem qkAccumulatorStoreOrder (hJoint : CorrectionJointGuards l X) {i store : EvId}
    {block : Fin 4} {frag : Fin 8} {d row col prior d' : Nat} {op op' : OperandSpec}
    {acc acc' : Bool} {mask mask' : List Nat} {cell : Cell}
    (hi : QkInstruction X i block frag d op acc mask)
    (hPrior : QkInstruction X (i.1,prior) block ⟨frag.val-1,by have := frag.isLt; omega⟩
      d' op' acc' mask') (hPrev : prior+1 = i.2) (hCell : resultCell op d row col = some cell)
    (hCurrent : X.MmaCell i cell) (hPrevious : X.MmaCell (i.1,prior) cell)
    (hStore : StoreCell l X store cell) :
    WriteBefore l X store (i.1,prior) ∨ ReadBefore l X .acc i store := by
  obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
  let stage := qkStage block
  have hOperand := hi.queryOperand hp hX
  obtain ⟨hRow,hCol⟩ := resultCell_rowcol hCell
  rw [hOperand.descriptor] at hRow hCol
  have hColumn : cell.column = scoreColumn stage+col := by
    exact congrArg Cell.column (Option.some.inj (hCell.symm.trans
      (hi.scoreCell hp hX ⟨row,hRow⟩ ⟨col,hCol⟩)))
  have hTile : tile = .probability stage := by
    have hLo := hFoot.columnLo
    have hHi := hFoot.columnHi
    change col < 128 at hCol
    have hStage := stage.isLt
    cases tile with
    | probability other =>
      have hOther := other.isLt
      have hEq : other = stage := by
        have hd := hColumn
        simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hLo hHi hd
        exact Fin.ext (by omega)
      rw [hEq]
    | rescale other =>
      have hd := hColumn
      simp only [TensorStoreTile.columns,outputColumn,scoreColumn] at hLo hd
      omega
  subst tile
  let hIssue : X.MmaIssue i d op acc mask := ⟨_,hi.decoded⟩
  have hOwner := (mmaWrittenCellCta hp hX hCurrent).symm.trans hFoot.cta
  have ⟨_,_,_,_,⟨_,hStoreEvent⟩,_,_⟩ := hStore
  have hSame : SameCta l i.1 store.1 :=
    ⟨event_thread_lt hX hi.decoded,event_thread_lt hX hStoreEvent,hOwner⟩
  obtain ⟨seen⟩ := probabilityStoreObservesScore hp hX stage hStore hFoot
  by_cases hEarlier : i.2 < seen.commit.2
  · exact .inr (.inr (.inl (seen.doneBeforeEarlierMma hp hX hIssue hSame hEarlier)))
  · have hNe := scoreCommitIndexNeMma hp hX seen.score hIssue hOwner
    have hPast : seen.commit.2 ≤ prior := by omega
    have hRepeat : 2 ≤ block.val := by
      by_contra! hFirst
      have hb : block = initialQkBlock stage := by
        apply Fin.ext
        change block.val = block.val%2
        omega
      exact hEarlier (initialScoreIssueBeforeCommit hp hX stage (hb ▸ hi) seen.score hOwner)
    have hGuard (packet : Fin 2) : ∃ w, MmaProbabilityAcquire l X (i.1,prior) stage packet w :=
      hPrior.recurringProbabilityAcquire hp hX hRepeat packet
    obtain ⟨_,_,_,_,_,_,hPreviousIssue,hWrite⟩ := hPrevious
    have hOverlap := mmaAccumulatorOnStoreTile hp hX hFoot hPreviousIssue
      (writeCell_resultCell hWrite)
    exact .inl (.inr (.inl
      (probabilityStoreReuseOrder hp hX hJoint stage hStore hFoot hOverlap seen hPast hGuard)))

/-- Every accumulating QK fragment reads the immediately preceding fragment of the same tile. -/
theorem qkAccumulatorReadsPriorFragment (hCuQ : Epilogue.DrainCuQProtected p X) {i : EvId}
    {block : Fin 4} {frag : Fin 8} {d row col : Nat} {op : OperandSpec} {acc : Bool}
    {mask : List Nat} {cell : Cell} (hi : QkInstruction X i block frag d op acc mask)
    (hFrag : 0 < frag.val) (hCell : resultCell op d row col = some cell) :
    ReadSource l X .acc (i.1,i.2-1) i cell := by
  obtain ⟨prior,d',op',acc',mask',hPrev,hPrior,hWritten,hBefore⟩ :=
    hi.accumulatorCandidateAdjacent hp hX hFrag hCell
  have hIdx : i.2-1 = prior := by omega
  rw [hIdx]
  have hCurrent := qkOwnsWrittenCell hp hX hi hCell
  have hAcc : acc = true := by rw [(hi.issueFlags hX).1,decide_eq_true (by omega)]
  have hRead : X.MmaReadCell i cell :=
    ⟨d,op,mask,row,col,⟨_,hAcc ▸ hi.decoded⟩,hCell⟩
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  obtain ⟨_,hLife⟩ := mmaAccessLifetime hp hX hCuQ (.inr (.inl hRead))
  refine ⟨fun h => (by omega : prior ≠ i.2) (congrArg Prod.snd h),
    .inl hWritten,hBefore,?_,fun c r hr hc free hf => .inl (hLife c r hr hc free hf)⟩
  intro other hOther
  rcases hOther with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
  · have ⟨_,_,_,_,_,_,hIssue,_⟩ := hMma
    have hCta := (mmaWrittenCellCta hp hX hMma).symm.trans
      (mmaWrittenCellCta hp hX hCurrent)
    have hLane := mmaIssueSameThread hp hX hIssue (show X.MmaIssue i d op acc mask from
      ⟨_,hi.decoded⟩) hCta
    rcases lt_trichotomy other.2 i.2 with hPast | hSame | hFuture
    · rcases lt_or_eq_of_le (show other.2 ≤ prior by omega) with h | h
      · exact .inr (.inl (.inl (.inr
          (mmaCellWriteOrderedAtEarlierIndex hp hX hGuard hMma hWritten h))))
      · exact .inl (Prod.ext hLane h)
    · exact .inr (.inr (.inl (Prod.ext hLane hSame)))
    · have hPipe := mmaCellWriteOrderedAtEarlierIndex hp hX hGuard hCurrent hMma hFuture
      exact .inr (.inr (.inr (.inr (pipelined_cRead_dWrite l X i other ▸ hPipe))))
  · rcases qkAccumulatorStoreOrder hp hX hJoint hi hPrior hPrev hCell hCurrent hWritten hStore
      with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
