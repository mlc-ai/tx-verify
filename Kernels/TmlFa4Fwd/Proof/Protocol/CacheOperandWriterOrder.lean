-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.Protocol.OperandOutputReuse
import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.TcMma Thread

set_option maxRecDepth 100000 in
/-- A shared B operand can compete only with other cache copies or with later
second-stage output staging that follows its MMA completion and proxy fence. -/
theorem cacheOperandOrderOfCopyOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma copy : EvId} {d index : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op accum mask) {loc : Loc}
    (hLoc : op.byteLoc .b index = some loc)
    (hCache : ∀ other spec, X.Copy other spec → spec.dst.Covers loc →
      other = copy ∨
        modelCausality l X loc (.async other (.write .copy)) (.async copy (.write .copy)) ∨
        modelCausality l X loc (.async mma (.mmaRead true index)) (.async other (.write .copy)))
    {other : Ref} {a : Acc} {data : List Byte} (hWrite : X.MemWrites other a data)
    (hCover : a.Covers loc) :
    other = .async copy (.write .copy) ∨
      modelCausality l X loc other (.async copy (.write .copy)) ∨
      modelCausality l X loc (.async mma (.mmaRead true index)) other := by
  have hFoot : X.MmaFootprint mma true index loc := .inl ⟨d,op,accum,mask,hMma,hLoc⟩
  have hBelow := mmaSharedOperandBand hp hX hFoot
  change l.sharedBase+68608 ≤ loc.addr at hBelow
  have hRange := mmaSharedByteRange hp hX hFoot
  rcases sharedWriteSource hX hWrite hCover hRange.space with hOrdinary | hTensor | hCopy
  · obtain ⟨writer,rfl,hWriter⟩ := hOrdinary
    rcases ordinarySharedWriteBelowOrStaging hp hX hWriter hCover hRange.space with
      hScratch | hStaging
    · have := hRange.lower
      omega
    obtain ⟨stage,box,col,row,hCol,hRow,rfl,hStore⟩ := hStaging.stageElement hp hX
    have hStage : stage = 1 := by
      by_contra hOther
      have hz : stage = 0 := Fin.ext (by have := stage.isLt; omega)
      subst stage
      have hEnd := (Thread.Output.elementStageRange hCol hRow hCover).2
      change loc.addr < l.sharedBase+68608 at hEnd
      omega
    subst stage
    have hAt : loc.cta = writer.1/l.block := hCover.2.1
    obtain ⟨_,_,hOrder⟩ := Output.mmaOperandBeforeSecondStagingOfSameCta hp hX hStore
      (hRange.cta.symm.trans hAt) hMma (isB := true) hLoc hRange.space hAt
    exact .inr (.inr hOrder)
  · obtain ⟨issuer,x,y,b,rfl⟩ := hTensor
    exact (tensorInputWriteDoesNotCoverKv hp hX hWrite hBelow hRange.upper hCover).elim
  · obtain ⟨issuer,spec,rfl,hIssue,rfl⟩ := hCopy
    rcases hCache issuer spec hIssue hCover with hSame | hEarlier | hLater
    · exact .inl (by rw [hSame])
    · exact .inr (.inl hEarlier)
    · exact .inr (.inr hLater)

end PTX.Kernels.TmlFa4Fwd.Protocol
