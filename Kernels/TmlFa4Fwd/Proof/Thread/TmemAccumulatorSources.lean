-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaFragmentHistory
public import Kernels.TmlFa4Fwd.Proof.Thread.QkIssueFlags
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaResultLayout
import Lemmas.Tcgen05.TcMmaIdealEval
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

private theorem writeResultCell {op : OperandSpec} {d row col : Nat} {cell : Cell}
    (hGroup : op.descriptor.group = .one) (hM : op.descriptor.m = 128)
    (hResult : resultCell op d row col = some cell) :
    writeCell op d (List.replicate 4 0) row col = some cell := by
  have hRow := (resultCell_rowcol hResult).1
  rw [hM] at hRow
  exact writeCell_no_mask_128 hGroup hM hRow (resultCell_bounds hResult).1 hResult

private theorem priorMmaWritesOperand {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i prior : EvId} {d d' row col : Nat} {op op' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell : Cell}
    (hi : X.MmaIssue i d op acc mask) (hPrev : X.MmaIssue prior d' op' acc' mask')
    (hSame : SameAccumulator d' op' d op) (hOrder : TraceBefore X prior i)
    (hGroup : op.descriptor.group = .one) (hGroup' : op'.descriptor.group = .one)
    (hM : op.descriptor.m = 128) (hM' : op'.descriptor.m = 128)
    (hV : Valid op.descriptor) (hV' : Valid op'.descriptor)
    (hMask : mask' = List.replicate 4 0) (hRead : resultCell op d row col = some cell) :
    X.MmaCell prior cell ∧ WriteBefore l X prior i := by
  have hCell : resultCell op' d' row col = some cell := by
    rw [resultCell_layoutD hGroup' hM' hV',hSame.1,hSame.2.2.1,hSame.2.2.2.1,
      ← resultCell_layoutD hGroup hM hV]
    exact hRead
  have hWrite : X.MmaCell prior cell := ⟨d',op',acc',mask',row,col,hPrev,
    hMask.symm ▸ writeResultCell hGroup' hM' hCell⟩
  obtain ⟨_,he⟩ := hi
  obtain ⟨_,hf⟩ := hPrev
  have hWarp : SameWarp l prior.1 i.1 :=
    ⟨⟨event_thread_lt hX hf,event_thread_lt hX he,by rw [hOrder.1]⟩,by rw [hOrder.1]⟩
  have hPo := po_of_not_access hOrder.1 hOrder.2.1 hOrder.2.2 (by rw [he]; rfl)
  exact ⟨hWrite,.inl (.inr ⟨hWarp,.inl (.single (.inl hPo)),
    d',op',acc',mask',d,op,acc,mask,⟨_,hf⟩,⟨_,he⟩,hSame⟩)⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The preceding event of an accumulating QK writes the same accumulator cell. -/
theorem QkInstruction.accumulatorCandidateAdjacent {i : EvId} {block : Fin 4} {frag : Fin 8}
    {d row col : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hi : QkInstruction X i block frag d op acc mask) (hPos : 0 < frag.val)
    (hCell : resultCell op d row col = some cell) :
    ∃ (k d' : Nat) (op' : OperandSpec) (acc' : Bool) (mask' : List Nat), k+1 = i.2 ∧
      QkInstruction X (i.1,k) block ⟨frag.val-1,by omega⟩ d' op' acc' mask' ∧
      X.MmaCell (i.1,k) cell ∧ WriteBefore l X (i.1,k) i := by
  obtain ⟨k,hEq,d',op',acc',mask',hPrior⟩ := hi.previousFragmentAdjacent hp hX hPos
  have hK : k < i.2 := by omega
  have hQ := hi.queryOperand hp hX
  have hQ' := hPrior.queryOperand hp hX
  have hSame : SameAccumulator d' op' d op :=
    ⟨(hPrior.scoreDestination hp hX).trans (hi.scoreDestination hp hX).symm,
      by rw [hQ'.descriptor,hQ.descriptor],by rw [hQ'.descriptor,hQ.descriptor],
      hQ'.ctaLow.trans hQ.ctaLow.symm,hQ'.ctaHigh.trans hQ.ctaHigh.symm⟩
  exact ⟨k,d',op',acc',mask',hEq,hPrior,priorMmaWritesOperand hX ⟨_,hi.decoded⟩ ⟨_,hPrior.decoded⟩
    hSame ⟨rfl,hK,len_of_get hi.decoded⟩
    (by rw [hQ.descriptor]; rfl) (by rw [hQ'.descriptor]; rfl)
    (by rw [hQ.descriptor]; rfl) (by rw [hQ'.descriptor]; rfl)
    (by rw [hQ.descriptor]; decide) (by rw [hQ'.descriptor]; decide)
    (hPrior.issueFlags hX).2 hCell⟩

/-- Each nonfirst QK fragment has an actual predecessor writing its accumulator cell. -/
theorem QkInstruction.accumulatorCandidate {i : EvId} {block : Fin 4} {frag : Fin 8}
    {d row col : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (hi : QkInstruction X i block frag d op acc mask) (hPos : 0 < frag.val)
    (hCell : resultCell op d row col = some cell) :
    ∃ prior, prior.1 = i.1 ∧ prior.2 < i.2 ∧
      X.MmaCell prior cell ∧ WriteBefore l X prior i := by
  obtain ⟨k,_,_,_,_,hEq,_,hWrite,hOrder⟩ := hi.accumulatorCandidateAdjacent hp hX hPos hCell
  exact ⟨(i.1,k),rfl,by omega,hWrite,hOrder⟩

private theorem pvAccumulatorOfPrior {i : EvId} {k : Nat} {block block' : Fin 4}
    {frag frag' : Fin 8} {d d' row col : Nat} {op op' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} {cell : Cell} (hi : PvInstruction X i block frag d op acc mask)
    (hPrior : PvInstruction X (i.1,k) block' frag' d' op' acc' mask')
    (hStage : (pvSite block').stage = (pvSite block).stage) (hK : k < i.2)
    (hCell : resultCell op d row col = some cell) :
    X.MmaCell (i.1,k) cell ∧ WriteBefore l X (i.1,k) i := by
  obtain ⟨_,_,hD,hLow,hHigh⟩ := hi.valueOperand hp hX
  obtain ⟨_,_,hD',hLow',hHigh'⟩ := hPrior.valueOperand hp hX
  have hSame : SameAccumulator d' op' d op :=
    ⟨(hPrior.outputDestination hp hX).trans
        ((congrArg outputColumn hStage).trans (hi.outputDestination hp hX).symm),
      by rw [hD',hD],by rw [hD',hD],hLow'.trans hLow.symm,hHigh'.trans hHigh.symm⟩
  exact priorMmaWritesOperand hX ⟨_,hi.decoded⟩ ⟨_,hPrior.decoded⟩
    hSame ⟨rfl,hK,len_of_get hi.decoded⟩ (by rw [hD]; rfl) (by rw [hD']; rfl)
    (by rw [hD]; rfl) (by rw [hD']; rfl)
    (by rw [hD]; decide) (by rw [hD']; decide) (hPrior.fixedOperandFields hX).2.2 hCell

/-- An accumulating PV has an actual prior writer in its visit or the carried visit. -/
theorem PvInstruction.accumulatorCandidate {i : EvId} {block : Fin 4} {frag : Fin 8}
    {d row col : Nat} {op : OperandSpec} {mask : List Nat} {cell : Cell}
    (hi : PvInstruction X i block frag d op true mask) (hCell : resultCell op d row col = some cell)
    :
    ∃ prior, prior.1 = i.1 ∧ prior.2 < i.2 ∧
      X.MmaCell prior cell ∧ WriteBefore l X prior i := by
  rcases (hi.accumulatorUse hp hX).mp rfl with hPos | hCarry
  · obtain ⟨k,hK,_,_,_,_,hPrior⟩ := hi.previousFragment hp hX hPos
    exact ⟨(i.1,k),rfl,hK,pvAccumulatorOfPrior hp hX hi hPrior rfl hK hCell⟩
  · obtain ⟨k,hK,_,_,_,_,hPrior⟩ := hi.previousSteadyFragment hp hX hCarry
    have hStage : (pvSite (firstPvBlock true (pvSite block).stage)).stage =
        (pvSite block).stage := by
      have audit : ∀ stage, (pvSite (firstPvBlock true stage)).stage = stage := by decide
      exact audit _
    exact ⟨(i.1,k),rfl,hK,pvAccumulatorOfPrior hp hX hi hPrior hStage hK hCell⟩

/-- Every actual accumulator read has a prior same-lane write into its cell. -/
theorem mmaAccumulatorCandidate {i : EvId} {cell : Cell} (hRead : X.MmaReadCell i cell) :
    ∃ prior, prior.1 = i.1 ∧ prior.2 < i.2 ∧
      X.MmaCell prior cell ∧ WriteBefore l X prior i := by
  obtain ⟨d,op,mask,row,col,hIssue,hCell⟩ := hRead
  rcases actualMmaInstruction hX hIssue with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
  · have hPos := Nat.pos_of_ne_zero (of_decide_eq_true (hQk.issueFlags hX).1.symm)
    exact hQk.accumulatorCandidate hp hX hPos hCell
  · exact hPv.accumulatorCandidate hp hX hCell

end PTX.Kernels.TmlFa4Fwd.Thread
