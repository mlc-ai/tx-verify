-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryOperand
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryStaging
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedQueryWriters
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCoverage
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open Thread.Loader (QuerySubbox querySubboxWriteRange queryTensorWriterUnique)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
include hp hX hDone

private theorem initialQueryByteStable (hFrame : OutputFootprint p X) {stage bank plane : Fin 2}
    {producer consumer commit wait issue d index : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hActive : producer / l.block < tilePrefix p p.batch * p.heads)
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait)
    (hInit : Thread.Mma.InitialQueryFragment X stage (producer, issue))
    (hMma : X.MmaIssue (producer, issue) d op accum mask) {tensor : EvId} {s : TensorCopy.Spec}
    (hBox : QuerySubbox p l X tensor bank plane s) {x y byte : Nat} {loc : Loc}
    (hWrite : TensorCopy.writeLoc s x y byte = some loc) (hLoc : op.byteLoc .a index = some loc)
    (hOwner : tensor.1 / l.block = producer / l.block) {other : Ref} {a : Acc} {bs : List Byte}
    (hOther : X.MemWrites other a bs) (hCover : a.Covers loc) :
    other = .async tensor (.write (.load x y byte)) ∨
      modelCausality l X loc (.async (producer, issue) (.mmaRead false index)) other := by
  obtain ⟨hShared, hCta, hLow, hHi⟩ := querySubboxWriteRange hBox hWrite
  have hStage := bank.isLt
  have hPlane := plane.isLt
  rcases sharedWriteBeforeCache hp hX hOther hCover hShared (by omega) with hThread | hTensor
  · obtain ⟨writer, rfl, hWriter⟩ := hThread
    rcases ordinarySharedWriteBelowOrStaging hp hX hWriter hCover hShared with hScratch | hStaging
    · omega
    obtain ⟨out, subbox, col, row, hc, hr, rfl, hStage⟩ := hStaging.stageElement hp hX
    obtain ⟨rfl, _, _, hWriterCta, _, _, _⟩ :=
      querySubboxOfCorrectionOverlap hBox hWrite hc hr hCover
    have hActive' := hWriterCta.symm.trans hOwner ▸ hActive
    have hLocCta := hCta.trans hWriterCta
    have hMmaCta := hOwner.symm.trans hWriterCta
    obtain ⟨hCuQ, hUsedK⟩ := hFrame.metadataProtected hp
    exact .inr (initialQueryReadBeforeStaging hp hX hDone hStage hActive' hCuQ hUsedK
      hPhase hInit hMma hLoc hShared hLocCta hMmaCta).2
  · obtain ⟨other, ox, oy, oby, rfl⟩ := hTensor
    obtain ⟨obs, addr, _, _, hInput, hOtherLoc, _, hSize, _⟩ := hOther
    rw [Acc.loc_of_one hCover hSize] at hOtherLoc
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      queryTensorWriterUnique hp hX hBox hWrite hInput hOtherLoc
    exact .inl rfl

/-- The actual initial QK issue's query byte comes from the packed launch input or zero fill.
Both the quantified shared writes and the query's actual acquire are discharged. -/
theorem initialQueryOperandByte (hFrame : OutputFootprint p X) {batch : Nat} {stage : Fin 2}
    {producer consumer commit wait issue : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch + 1) * p.heads)
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait) (step : Fin 8)
    {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hByte : byte < 2) {d : Nat} {accum : Bool}
    {mask : List Nat} (hInit : Thread.Mma.InitialQueryFragment X stage (producer, issue))
    (hMma : X.MmaIssue (producer, issue) d
      (qkOperands l producer (Softmax.firstQkBlock stage) step 0) accum mask) :
    let coords := Epilogue.assignedCoordinates p batch (producer / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
    ∃ loc, (qkOperands l producer (Softmax.firstQkBlock stage) step 0).byteLoc .a
      (qkByteIndex row k byte) = some loc ∧
      OperandByteSource l X (producer, issue) false (qkByteIndex row k byte) loc
        ((Value.float .bf16 (qkQuery p (firstQ + row) coords.2
          (16 * step.val + k))).byteAt byte) := by
  dsimp only
  let block := Softmax.firstQkBlock stage
  let coords := Epilogue.assignedCoordinates p batch (producer / l.block)
  let plane : Fin 2 := ⟨qkPlane step, by unfold qkPlane; have := step.isLt; omega⟩
  let firstQ := p.qOffset batch + 256 * coords.1 + 128 * (qkStage block).val
  let spec := qInputSpec p (64 * plane.val) firstQ coords.2
    ⟨.shared, producer / l.block, qStart l (qkStage block) + 16384 * plane.val⟩
    (Output.queryObject l (producer / l.block) (qkStage block)) false
  let slot := qkQSlot p step hr hk hByte
  let loc := spec.sharedLoc slot
  obtain ⟨qWait, phase, hAcquire, hPhaseQ, hBefore⟩ := initialQueryAcquirePhase hp hX hInit
  have hStage : qkStage block = stage := Softmax.firstQkBlock_stage stage
  rw [← hStage] at hAcquire hPhaseQ
  obtain ⟨tensor, hTensor, hNotify, hLoc, hValue⟩ :=
    qkQueryOperandOfObservedAcquire hp hX hDone hFrame block step hb hLo hHi
      hr hk hByte hAcquire hPhaseQ hBefore hMma
  have hIssue' : X.TensorIssue tensor p.qMapAddress spec := hTensor
  have hOwner : tensor.1 / l.block = producer / l.block := by
    exact ((actualMbarOperand hp hX (Execution.UsesMbar.of_tensor hIssue')).1).symm
  have hBox : QuerySubbox p l X tensor (qkStage block) plane spec := by
    refine ⟨hIssue', ?_, ?_, rfl, rfl, rfl, rfl⟩
    · change Output.queryObject l (producer / l.block) (qkStage block) = _
      rw [hOwner]
    · change Loc.mk .shared (producer / l.block)
        (qStart l (qkStage block) + 16384 * plane.val) = _
      rw [hOwner]
  have hWrite : TensorCopy.writeLoc spec slot.1.val row byte = some loc := by
    have hs : TensorTransfer.slotAt spec.descriptor slot.1.val row byte = some slot :=
      TensorCopy.slotAt_self slot
    exact congrArg (Option.map spec.sharedLoc) hs
  have hActive : producer / l.block < tilePrefix p p.batch * p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))
  have hValue' := hValue (fun _ _ _ hw hc =>
    (initialQueryByteStable hp hX hDone hFrame hActive hPhase hInit hMma
      hBox hWrite hLoc hOwner hw hc).elim .inl (.inr ∘ .inr))
  exact ⟨loc, hLoc, by simpa only [block, Softmax.firstQkBlock_stage] using hValue'⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
