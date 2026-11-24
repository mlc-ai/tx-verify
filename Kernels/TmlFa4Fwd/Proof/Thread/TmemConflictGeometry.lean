-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma
open PTX.Kernels.TmlFa4Fwd.Mma

/-- The MMA accumulator occupying the store's tile. -/
def MmaAccumulatorOn (X : Execution) (i : EvId) (cell : Cell) : TensorStoreTile → Prop
  | .probability stage =>
    ∃ block step d op accum mask row col, qkStage block = stage ∧
      QkInstruction X i block step d op accum mask ∧ resultCell op d row col = some cell
  | .rescale stage =>
    ∃ block step d op accum mask row col, (pvSite block).stage = stage ∧
      PvInstruction X i block step d op accum mask ∧ resultCell op d row col = some cell

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The accumulator covering a cell in a probability or rescale tile. -/
theorem mmaAccumulatorOnTile (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d row col : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat} {cell : Cell}
    {tile : TensorStoreTile} (hColumn : tile.columns.1 ≤ cell.column ∧ cell.column < tile.columns.2)
    (hi : X.MmaIssue i d op accum mask) (hc : resultCell op d row col = some cell) :
    MmaAccumulatorOn X i cell tile := by
  rcases actualMmaInstruction hX hi with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · have hShape := hQk.queryOperand hp hX
    have hm : 128 = op.descriptor.m := by rw [hShape.descriptor]; rfl
    have hn : 128 = op.descriptor.n := by rw [hShape.descriptor]; rfl
    obtain ⟨hRow,hCol⟩ := resultCell_rowcol hc
    have hCell := hQk.scoreCell hp hX ⟨row,hm.symm ▸ hRow⟩ ⟨col,hn.symm ▸ hCol⟩
    have hExact : cell.column = scoreColumn (qkStage block)+col :=
      congrArg Cell.column (Option.some.inj (hc.symm.trans hCell))
    have hcBound : col < 128 := hn.symm ▸ hCol
    have hFst := hColumn.1
    have hLast := hColumn.2
    cases tile with
    | probability stage =>
      have hStage : qkStage block = stage := by
        apply Fin.ext
        simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hFst hLast
        unfold scoreColumn at hExact
        omega
      exact ⟨block,step,d,op,accum,mask,row,col,hStage,hQk,hc⟩
    | rescale stage =>
      have hWidth := scoreColumn_range (qkStage block)
      simp only [TensorStoreTile.columns,outputColumn] at hFst
      omega
  · obtain ⟨_,_,hShape,hLo,hHi⟩ := hPv.valueOperand hp hX
    have hm : 128 = op.descriptor.m := by rw [hShape]; rfl
    have hn : 128 = op.descriptor.n := by rw [hShape]; rfl
    obtain ⟨hRow,hCol⟩ := resultCell_rowcol hc
    have hCell := hPv.outputCell hp hX ⟨row,hm.symm ▸ hRow⟩ ⟨col,hn.symm ▸ hCol⟩
    have hExact : cell.column = outputColumn (pvSite block).stage+col :=
      congrArg Cell.column (Option.some.inj (hc.symm.trans hCell))
    have hcBound : col < 128 := hn.symm ▸ hCol
    have hFst := hColumn.1
    have hLast := hColumn.2
    cases tile with
    | probability stage =>
      have hWidth := scoreColumn_range stage
      have hEnd := probabilityColumn_range stage
      simp only [TensorStoreTile.columns] at hLast
      unfold outputColumn at hExact
      omega
    | rescale stage =>
      have hStage : (pvSite block).stage = stage := by
        apply Fin.ext
        simp only [TensorStoreTile.columns,outputColumn] at hFst hLast
        unfold outputColumn at hExact
        omega
      exact ⟨block,step,d,op,accum,mask,row,col,hStage,hPv,hc⟩

/-- Every actual MMA accumulator sharing a store cell belongs to the same physical stage. -/
theorem mmaAccumulatorOnStoreTile (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i store : EvId} {d row col : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    {cell : Cell} {tile : TensorStoreTile} (ht : TensorStoreFootprint l store cell tile)
    (hi : X.MmaIssue i d op accum mask) (hc : resultCell op d row col = some cell) :
    MmaAccumulatorOn X i cell tile :=
  mmaAccumulatorOnTile hp hX ⟨ht.columnLo,ht.columnHi⟩ hi hc

private theorem mmaOperandCtas (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue i d op acc mask) :
    op.lowCta = i.1/l.block ∧ op.highCta = i.1/l.block := by
  rcases actualMmaInstruction hX hi with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · have hShape := hQk.queryOperand hp hX
    exact ⟨hShape.ctaLow,hShape.ctaHigh⟩
  · obtain ⟨_,_,_,hLow,hHigh⟩ := hPv.valueOperand hp hX
    exact ⟨hLow,hHigh⟩

private theorem aCellCta {op : OperandSpec} {index byte : Nat} {cell : Cell} {cta : Nat}
    (hLo : op.lowCta = cta) (hHi : op.highCta = cta)
    (hi : aCell op index = some (cell,byte)) : cell.cta = cta := by
  unfold aCell at hi
  dsimp only at hi
  cases ha : op.aTmem with
  | none => simp [ha] at hi
  | some address =>
    simp only [ha,Option.bind_some] at hi
    split at hi
    · obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj hi)
      simp [hLo,hHi]
    · cases hi

/-- A physical A operand cell resides in the CTA of its issuing MMA. -/
theorem mmaAOperandCta (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {cell : Cell} (hi : X.MmaACell i cell) : cell.cta = i.1/l.block := by
  obtain ⟨d,op,acc,mask,index,byte,hIssue,hCell⟩ := hi
  obtain ⟨hLow,hHigh⟩ := mmaOperandCtas hp hX hIssue
  exact aCellCta hLow hHigh hCell

/-- A physical result cell resides in the CTA of its issuing MMA. -/
theorem mmaWrittenCellCta (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {cell : Cell} (hi : X.MmaCell i cell) : cell.cta = i.1/l.block := by
  obtain ⟨d,op,acc,mask,row,col,hIssue,hCell⟩ := hi
  obtain ⟨hLow,hHigh⟩ := mmaOperandCtas hp hX hIssue
  rcases resultCell_cta (writeCell_resultCell hCell) with hCta | hCta
  · exact hCta.trans hLow
  · exact hCta.trans hHigh

/-- A and D accesses to one cell are issued by the same lane of the CTA. -/
theorem mmaAAndDLane (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {reader writer : EvId} {cell : Cell} (hr : X.MmaACell reader cell) (hw : X.MmaCell writer cell)
    : reader.1 = writer.1 := by
  have hCta := (mmaAOperandCta hp hX hr).symm.trans (mmaWrittenCellCta hp hX hw)
  obtain ⟨_,_,_,_,_,_,hR,_⟩ := hr
  obtain ⟨_,_,_,_,_,_,hW,_⟩ := hw
  exact mmaIssueSameThread hp hX hR hW hCta

/-- An actual Tensor Memory A read is pipeline-ordered before a later MMA write. -/
theorem earlierMmaAOperandOrdered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {reader writer : EvId} {cell : Cell} (hr : X.MmaACell reader cell) (hw : X.MmaCell writer cell)
    (hBefore : reader.2 < writer.2) :
    ReadBefore l X .a reader writer := by
  have hLane := mmaAAndDLane hp hX hr hw
  obtain ⟨d,op,acc,mask,index,byte,⟨site,hR⟩,hCell⟩ := hr
  obtain ⟨d',op',acc',mask',row,col,⟨site',hW⟩,_⟩ := hw
  have hState : op.aTmem.isSome := by
    cases h : op.aTmem with
    | none => simp [aCell,h] at hCell
    | some _ => rfl
  have hPo := po_of_not_access hLane hBefore (len_of_get hW) (by rw [hW]; rfl)
  have hWarp : SameWarp l reader.1 writer.1 :=
    ⟨⟨event_thread_lt hX hR,event_thread_lt hX hW,congrArg (·/l.block) hLane⟩,by rw [hLane]⟩
  have hA : Pipelined l X .aRead reader .dWrite writer :=
    ⟨hWarp,.inl (.single (.inl hPo)),⟨d,op,acc,mask,⟨site,hR⟩,hState⟩,
      d',op',acc',mask',site',hW⟩
  exact .inr (.inr (.inl hA))

end PTX.Kernels.TmlFa4Fwd.Thread
