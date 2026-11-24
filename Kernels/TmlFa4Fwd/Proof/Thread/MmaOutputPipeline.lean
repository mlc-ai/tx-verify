-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQkDestination
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
public import Core.Tc.TcMmaOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma

private theorem resultFootprint {l : Launch} {i : EvId} {d row col : Nat}
    {s : TcMma.OperandSpec} {cell : TcMma.Cell}
    (hm : s.descriptor.m = 128) (hn : s.descriptor.n = 128)
    (hGeom : ∀ r c : Fin 128, TcMma.resultCell s d r.val c.val =
      some ⟨i.1/l.block,r.val,d+c.val⟩)
    (hc : TcMma.resultCell s d row col = some cell) :
    cell.cta = i.1/l.block ∧ d ≤ cell.column ∧ cell.column < d+128 := by
  obtain ⟨hr,hc'⟩ := TcMma.resultCell_rowcol hc
  rw [hm] at hr
  rw [hn] at hc'
  have h := hGeom ⟨row,hr⟩ ⟨col,hc'⟩
  obtain rfl := Option.some.inj (hc.symm.trans h)
  exact ⟨rfl,Nat.le_add_right _ _,Nat.add_lt_add_left hc' _⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem actualResultGeometry {i : EvId} {d row col : Nat} {s : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {cell : TcMma.Cell} (hi : X.MmaIssue i d s accum mask)
    (hc : TcMma.resultCell s d row col = some cell) :
    (∃ bank, d = 128*bank) ∧ s.descriptor.m = 128 ∧ s.descriptor.n = 128 ∧
      s.lowCta = i.1/l.block ∧ s.highCta = i.1/l.block ∧
      cell.cta = i.1/l.block ∧ d ≤ cell.column ∧ cell.column < d+128 := by
  rcases actualMmaInstruction hX hi with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · have hd := hQk.scoreDestination hp hX
    have hShape := hQk.queryOperand hp hX
    have hm : s.descriptor.m = 128 := by rw [hShape.descriptor]; rfl
    have hn : s.descriptor.n = 128 := by rw [hShape.descriptor]; rfl
    have hGeom r c := hQk.scoreCell hp hX r c
    simp only [← hd] at hGeom
    exact ⟨⟨(qkStage block).val,hd⟩,hm,hn,hShape.ctaLow,hShape.ctaHigh,
      resultFootprint hm hn hGeom hc⟩
  · have hd := hPv.outputDestination hp hX
    obtain ⟨_,_,hShape,hLow,hHigh⟩ := hPv.valueOperand hp hX
    have hm : s.descriptor.m = 128 := by rw [hShape]; rfl
    have hn : s.descriptor.n = 128 := by rw [hShape]; rfl
    have hGeom r c := hPv.outputCell hp hX r c
    simp only [← hd] at hGeom
    have hBank : d = 128*(2+(pvSite block).stage.val) := by
      rw [hd]
      simp [outputColumn, Nat.mul_add]
    exact ⟨⟨2+(pvSite block).stage.val,hBank⟩,hm,hn,hLow,hHigh,
      resultFootprint hm hn hGeom hc⟩

private theorem mmaOverlappingResultPipeline {i j : EvId} {d d' row col row' col' : Nat}
    {s s' : TcMma.OperandSpec} {accum accum' : Bool} {mask mask' : List Nat} {cell : TcMma.Cell}
    (hi : X.MmaIssue i d s accum mask) (hj : X.MmaIssue j d' s' accum' mask')
    (hI : TcMma.resultCell s d row col = some cell)
    (hJ : TcMma.resultCell s' d' row' col' = some cell) (hNe : i ≠ j) :
    TcMma.Pipelined l X .dWrite i .dWrite j ∨ TcMma.Pipelined l X .dWrite j .dWrite i := by
  obtain ⟨⟨bank,hd⟩,hm,hn,hLo,hHi,hCta,hFirst,hLast⟩ := actualResultGeometry hp hX hi hI
  obtain ⟨⟨bank',hd'⟩,hm',hn',hLo',hHi',hCta',hFirst',hLast'⟩ :=
    actualResultGeometry hp hX hj hJ
  have hSame := hCta.symm.trans hCta'
  exact mmaDestinationPipeline hp hX hi hj hSame hNe
    ⟨by omega,hm.trans hm'.symm,hn.trans hn'.symm,hLo.trans (hSame.trans hLo'.symm),
      hHi.trans (hSame.trans hHi'.symm)⟩

/-- Any two distinct actual MMA operations that write the same cell are pipeline-ordered. -/
theorem overlappingMmaOutputPipeline {i j : EvId} {cell : TcMma.Cell} (hi : X.MmaCell i cell)
    (hj : X.MmaCell j cell) (hNe : i ≠ j) : TcMma.Pipelined l X .dWrite i .dWrite j ∨
      TcMma.Pipelined l X .dWrite j .dWrite i := by
  obtain ⟨d,s,accum,mask,row,col,hI,hCell⟩ := hi
  obtain ⟨d',s',accum',mask',row',col',hJ,hCell'⟩ := hj
  exact mmaOverlappingResultPipeline hp hX hI hJ (TcMma.writeCell_resultCell hCell)
    (TcMma.writeCell_resultCell hCell') hNe

/-- The write-write race check between actual MMA results follows from their D pipeline order. -/
theorem mmaWritesOrdered {i j : EvId} {cell : TcMma.Cell} (hi : X.MmaCell i cell)
    (hj : X.MmaCell j cell) :
    i = j ∨ TcMma.WriteBefore l X i j ∨ TcMma.WriteBefore l X j i := by
  by_cases hNe : i = j
  · exact .inl hNe
  · rcases overlappingMmaOutputPipeline hp hX hi hj hNe with h | h
    · exact .inr (.inl (.inl (.inr h)))
    · exact .inr (.inr (.inl (.inr h)))

/-- A C read and an MMA write of one cell share the same accumulator pipeline. -/
theorem mmaAccumulatorReadOrdered {reader writer : EvId} {cell : TcMma.Cell}
    (hr : X.MmaReadCell reader cell) (hw : X.MmaCell writer cell) :
    reader = writer ∨ TcMma.WriteBefore l X writer reader ∨
      TcMma.ReadBefore l X .acc reader writer := by
  by_cases hNe : reader = writer
  · exact .inl hNe
  · obtain ⟨d,s,mask,row,col,hR,hRead⟩ := hr
    obtain ⟨d',s',accum',mask',row',col',hW,hWrite⟩ := hw
    rcases mmaOverlappingResultPipeline hp hX hR hW hRead (TcMma.writeCell_resultCell hWrite)
      hNe with h | h
    · exact .inr (.inr (.inr (.inr (TcMma.pipelined_cRead_dWrite .. ▸ h))))
    · exact .inr (.inl (.inl (.inr h)))

end PTX.Kernels.TmlFa4Fwd.Thread
