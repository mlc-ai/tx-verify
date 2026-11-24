-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryOperand
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryStaging
public import Kernels.TmlFa4Fwd.Proof.Safety.StagingOperandOrder
public import Lemmas.Tcgen05.MmaSources
import Kernels.TmlFa4Fwd.Proof.Thread.ObservedQueryWriters
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCoverage
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryInput
import Kernels.TmlFa4Fwd.Proof.InputCopies
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy PTX.TcMma Thread Protocol Thread.Correction
open PTX.Kernels.TmlFa4Fwd.Mma
open Thread.Loader (QuerySubbox querySubboxWriteRange queryTensorWriterUnique)

private theorem stageZeroWritesOfElement {X : Execution} {writer : EvId} {a : Acc}
    {data : List Byte} (hStage : StageStagingWrite X writer 0 a data) :
    StageZeroStagingWrites X writer a data := by
  obtain ⟨box,chunk,he⟩ := hStage.decoded
  exact StageZeroStagingWrites.of_event box chunk he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A stage-zero store follows the overlapping shared operand read at that byte. -/
private theorem stageZeroStagingAfterOperand {mma writer : EvId} {a : Acc} {bytes : List Byte}
    {loc : Loc} {d index : Nat} {op : TcMma.OperandSpec} {isB acc : Bool} {mask : List Nat}
    (hStore : StageStagingWrite X writer 0 a bytes) (hCover : a.Covers loc)
    (hShared : loc.space = .shared) (hCta : mma.1/l.block = writer.1/l.block)
    (hIssue : X.MmaIssue mma d op acc mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) :
    modelCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer) := by
  obtain ⟨_,_,_,_,_,_,_,hOrder⟩ := observedOperandBeforeFirstStaging hp hX
    (stageZeroWritesOfElement hStore) hIssue hCta hLoc hCover hShared
  exact hOrder

omit hp hX in
private theorem querySubboxSignedSpec {p : Params} {l : Launch} {X : Execution}
    {i : EvId} {stage plane : Fin 2} {s : TensorCopy.Spec}
    (hBox : QuerySubbox p l X i stage plane s) :
    ∃ origin : Fin 3 → Int,
      s = ⟨⟨2,p.qMap,origin,
        ⟨.shared,i.1/l.block,qStart l stage+16384*plane.val⟩,none⟩,
        Output.queryObject l (i.1/l.block) stage,false,.one⟩ := by
  obtain ⟨_,hBar,hShared,hDesc,hRows,hCluster,hGroup⟩ := hBox
  rcases s with ⟨⟨outer,desc,origin,shared,rows⟩,barrier,cluster,group⟩
  simp only [Sigma.mk.injEq] at hDesc
  obtain ⟨rfl,hDesc⟩ := hDesc
  obtain rfl := eq_of_heq hDesc
  dsimp only at hBar hShared hRows hCluster hGroup
  subst barrier shared rows cluster group
  exact ⟨origin,rfl⟩

private theorem queryOperandOtherWriter {mma tensor : EvId} {stage plane : Fin 2}
    {s : TensorCopy.Spec} (hBox : QuerySubbox p l X tensor stage plane s)
    (hOwner : tensor.1/l.block = mma.1/l.block) {index x y byte : Nat} {loc : Loc}
    (hWrite : TensorCopy.writeLoc s x y byte = some loc)
    (hStagingAfter : ∀ writer a data, StageStagingWrite X writer 0 a data →
      a.Covers loc → a.size ≠ 1 → loc.space = .shared →
      mma.1 / l.block = writer.1 / l.block →
      modelCausality l X loc (.async mma (.mmaRead false index)) (.thread writer)) :
    ∀ other a data, X.MemWrites other a data → a.Covers loc →
      other = .async tensor (.write (.load x y byte)) ∨
      modelCausality l X loc (.async mma (.mmaRead false index)) other := by
  intro other a data hOther hCover
  obtain ⟨hShared,hCta,hLo,hHi⟩ := querySubboxWriteRange hBox hWrite
  have hStage := stage.isLt
  have hPlane := plane.isLt
  rcases sharedWriteBeforeCache hp hX hOther hCover hShared (by omega) with hThread | hTensor
  · obtain ⟨writer,rfl,hWriter⟩ := hThread
    rcases ordinarySharedWriteBelowOrStaging hp hX hWriter hCover hShared with hScratch | hStaging
    · omega
    obtain ⟨out,subbox,col,row,hCol,hRow,rfl,hStore⟩ := hStaging.stageElement hp hX
    obtain ⟨rfl,_,_,hWriterCta,_,_,_⟩ :=
      querySubboxOfCorrectionOverlap hBox hWrite hCol hRow hCover
    exact .inr (hStagingAfter writer _ _ hStore hCover (by change 4 ≠ 1; decide) hShared
      (hOwner.symm.trans hWriterCta))
  · obtain ⟨issue,ox,oy,oby,rfl⟩ := hTensor
    obtain ⟨obs,addr,_,_,hInput,hOtherLoc,_,hSize,_⟩ := hOther
    rw [Acc.loc_of_one hCover hSize] at hOtherLoc
    obtain ⟨rfl,rfl,rfl,rfl⟩ := queryTensorWriterUnique hp hX hBox hWrite hInput hOtherLoc
    exact .inl rfl

/-- A query byte that the MMA has yet to read has no competing staging write.
An overlapping stage-zero write would already have observed the read's completion. -/
private theorem pendingQueryOtherWriter (hCuQ : Epilogue.DrainCuQProtected p X) {mma tensor : EvId}
    {stage plane : Fin 2} {s : TensorCopy.Spec} (hBox : QuerySubbox p l X tensor stage plane s)
    (hOwner : tensor.1 / l.block = mma.1 / l.block) {d index x y byte : Nat} {op : OperandSpec}
    {acc : Bool} {mask : List Nat} {loc : Loc} (hMma : X.MmaIssue mma d op acc mask)
    (hAt : op.byteLoc .a index = some loc) (hWrite : TensorCopy.writeLoc s x y byte = some loc)
    (hPending : X.async.mmaOperands mma = none) :
    ∀ w a data, X.MemWrites w a data → a.Covers loc →
      w = .async tensor (.write (.load x y byte)) ∨
        modelCausality l X loc (.async mma (.mmaRead false index)) w := by
  apply queryOperandOtherWriter hp hX hBox hOwner hWrite
  intro writer a bytes hStore hCover _ hShared hCta
  obtain ⟨⟨_, _, operands, hOperands, _⟩, _⟩ :=
    firstStagingCannotPrecedeObservedOperand hp hX hCuQ
      (stageZeroWritesOfElement hStore) hMma hCta (isB := false) hAt hCover hShared
  rw [hPending] at hOperands
  cases hOperands

private theorem actualQkQueryElementOfStagingOrder (hFrame : OutputFootprint p X) {i : EvId}
    {block : Fin 4} {step : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hQk : QkInstruction X i block step d op acc mask)
    (hStagingAfter : ∀ writer a data loc index, StageStagingWrite X writer 0 a data →
      a.Covers loc → a.size ≠ 1 → loc.space = .shared → i.1/l.block = writer.1/l.block →
      op.byteLoc .a index = some loc →
      modelCausality l X loc (.async i (.mmaRead false index)) (.thread writer)) {ops : MmaOperands}
    (hOps : X.async.mmaOperands i = some ops) {row k : Nat} (hr : row < 128) (hk : k < 16) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok value := by
  let stage := qkStage block
  let plane : Fin 2 := ⟨qkPlane step,by unfold qkPlane; have := step.isLt; omega⟩
  obtain ⟨wait,e,he,hWait,hBefore⟩ := hQk.queryAcquire hp hX
  obtain ⟨acquire,phase,_,hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e,he,hWait⟩
  obtain ⟨tensor,s,hWaitCta,hBox,hNotify⟩ := acquire.observedSubbox hp hX hPhase plane
  have hOwner := hWaitCta.trans (congrArg (·/l.block) hBefore.1)
  obtain ⟨origin,rfl⟩ := querySubboxSignedSpec hBox
  let shared : Loc := ⟨.shared,tensor.1/l.block,qStart l stage+16384*plane.val⟩
  let barrier := Output.queryObject l (tensor.1/l.block) stage
  let spec : TensorCopy.Spec := ⟨⟨2,p.qMap,origin,shared,none⟩,barrier,false,.one⟩
  have hRead := acquire.observesTensor hp hX hWaitCta hPhase hNotify
  obtain ⟨o,_,ho,hActual,hFinished,_⟩ := hRead.tensor
  obtain ⟨_,hAct⟩ := hActual
  obtain ⟨_,hBoxIssue⟩ := hBox.1
  have hSpec : o.spec = spec :=
    (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hAct.symm.trans hBoxIssue)))).2
  let first := qkQSlot p step hr hk (show 0 < 2 by decide)
  obtain ⟨value,hValue⟩ := qInputWordWritten hp hX hFrame ho hFinished hSpec first.1 first.2.1
  let hIssue : X.MmaIssue i d op acc mask := ⟨_,hQk.decoded⟩
  have hQ := hQk.queryOperand hp hX
  have hActualByte (byte : Fin 2) :
      ops.a[qkByteIndex row k byte.val]? =
        some (some ((Value.float .bf16 value).byteAt byte.val)) := by
    let slot := qkQSlot p step hr hk byte.isLt
    let loc := spec.sharedLoc slot
    have hAddress := qkQInputSlot hp i.1 block step 0 0 0 barrier false hr hk byte.isLt
    have hSame : op.byteLoc .a (qkByteIndex row k byte.val) =
        (qkOperands l i.1 block step 0).byteLoc .a (qkByteIndex row k byte.val) := by
      simp only [OperandSpec.byteLoc,hQ.descriptor,hQ.address,hQ.ctaLow,hQ.ctaHigh,
        hQ.shared,qkOperands]
      rfl
    have hLoc : op.byteLoc .a (qkByteIndex row k byte.val) = some loc := by
      rw [hSame,hAddress]
      simp only [loc,spec,shared,hOwner,qInputSpec,TensorBox.sharedLoc,plane,stage,slot]
    have hWrite : TensorCopy.writeLoc spec slot.1.val row byte.val = some loc := by
      rw [TensorCopy.writeLoc]
      exact congrArg (Option.map spec.sharedLoc) (TensorCopy.slotAt_self slot)
    have hObject : spec.mbar = Output.queryObject l (wait.1/l.block) stage := by
      change barrier = _
      rw [← hWaitCta]
    have hOrder := queryBeforeOperand hp hX hBox.1 hObject
      acquire hPhase hNotify hBefore hWrite hIssue hLoc
    have hSource : OperandByteSource l X i false (qkByteIndex row k byte.val) loc
        ((Value.float .bf16 value).byteAt byte.val) := by
      refine ⟨_,{loc,size := 1},_,hValue byte,⟨rfl,rfl,le_rfl,Nat.lt_succ_self _⟩,
        by simp [wbyte],hOrder,?_⟩
      intro other a data hw hc
      have hOrder := queryOperandOtherWriter hp hX hBox hOwner hWrite
        (fun writer a data hStore hCover hSize hShared hCta =>
          hStagingAfter writer a data loc _ hStore hCover hSize hShared hCta hLoc)
        other a data hw hc
      exact hOrder.elim .inl (.inr ∘ .inr)
    exact operandByte_observed hX hIssue hOps (isB := false) hLoc hSource
  exact ⟨value,idealBf16Element_of_bytes (hActualByte 0) (hActualByte 1)⟩

/-- Every recorded QK A element is BF16 on a guarded prefix. The descriptor origin
determines the value or the Q zero fill. -/
theorem actualQkQueryElement (hFrame : OutputFootprint p X) {i : EvId} {block : Fin 4}
    {step : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hQk : QkInstruction X i block step d op acc mask) {ops : MmaOperands}
    (hOps : X.async.mmaOperands i = some ops) {row k : Nat} (hr : row < 128) (hk : k < 16) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok value :=
  actualQkQueryElementOfStagingOrder hp hX hFrame hQk
    (fun _ _ _ _ _ hStore hCover _ hShared hCta hLoc =>
      stageZeroStagingAfterOperand hp hX hStore hCover hShared hCta ⟨_,hQk.decoded⟩ hLoc) hOps hr hk

/-- Before a QK issue reads its operands, each query byte already has a completed writer.
No later staging store competes with this source in that prefix. -/
theorem pendingQkQuerySource (hFrame : OutputFootprint p X) {i : EvId} {block : Fin 4}
    {step : Fin 8} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hQk : QkInstruction X i block step d op acc mask) (hPending : X.async.mmaOperands i = none)
    {index : Nat} {loc : Loc} (hAt : op.byteLoc .a index = some loc) :
    ∃ src : MmaSources.ByteSource X, src.loc = loc ∧
      ∀ w a data, X.MemWrites w a data → a.Covers loc →
        w = src.ref ∨ modelCausality l X loc w src.ref ∨
          modelCausality l X loc (.async i (.mmaRead false index)) w := by
  have hCuQ : Epilogue.DrainCuQProtected p X := hp.cuQ_protected (fun _ _ _ _ =>
    Thread.Loader.loaderOutputWrites hFrame)
  have hQ := hQk.queryOperand hp hX
  have hIndex : index < 4096 := by
    simpa [hQ.descriptor, qkDescriptor, TcMma.Operand.rows, TcMma.Operand.extent,
      TcMma.Kind.k, TcMma.Kind.width] using TcMma.OperandSpec.byteLoc_index_lt hAt
  let row := index / 32
  let k := (index / 2) % 16
  let byte := index % 2
  have hr : row < 128 := by dsimp [row]; omega
  have hk : k < 16 := Nat.mod_lt _ (by decide)
  have hb : byte < 2 := Nat.mod_lt _ (by decide)
  have hDecode : qkByteIndex row k byte = index := by
    simp only [qkByteIndex, row, k, byte]
    omega
  let stage := qkStage block
  let plane : Fin 2 := ⟨qkPlane step, by unfold qkPlane; have := step.isLt; omega⟩
  obtain ⟨wait, event, he, hw, hBefore⟩ := hQk.queryAcquire hp hX
  obtain ⟨acquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨event, he, hw⟩
  obtain ⟨tensor, s, hCta, hBox, hNotify⟩ := acquire.observedSubbox hp hX hPhase plane
  have hOwner := hCta.trans (congrArg (· / l.block) hBefore.1)
  obtain ⟨origin, rfl⟩ := querySubboxSignedSpec hBox
  let shared : Loc := ⟨.shared, tensor.1 / l.block, qStart l stage + 16384 * plane.val⟩
  let barrier := Output.queryObject l (tensor.1 / l.block) stage
  let spec : TensorCopy.Spec := ⟨⟨2, p.qMap, origin, shared, none⟩, barrier, false, .one⟩
  obtain ⟨o, _, ho, hActual, hFinished, _⟩ :=
    (acquire.observesTensor hp hX hCta hPhase hNotify).tensor
  obtain ⟨_, hAct⟩ := hActual
  obtain ⟨_, hBoxIssue⟩ := hBox.1
  have hSpec : o.spec = spec :=
    (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hAct.symm.trans hBoxIssue)))).2
  let slot := qkQSlot p step hr hk hb
  have hSame : op.byteLoc .a index = (qkOperands l i.1 block step 0).byteLoc .a index := by
    simp only [OperandSpec.byteLoc, hQ.descriptor, hQ.address, hQ.ctaLow, hQ.ctaHigh,
      hQ.shared, qkOperands]
    rfl
  have hLoc : spec.sharedLoc slot = loc := by
    have hAddress := qkQInputSlot hp i.1 block step 0 0 0 barrier false hr hk hb
    rw [hDecode] at hAddress
    rw [hSame, hAddress] at hAt
    simpa only [spec, shared, hOwner, qInputSpec, TensorBox.sharedLoc, plane, stage, slot]
      using Option.some.inj hAt
  have hWrite : TensorCopy.writeLoc spec slot.1.val row byte = some loc := by
    rw [← hLoc, TensorCopy.writeLoc]
    exact congrArg (Option.map spec.sharedLoc) (TensorCopy.slotAt_self slot)
  obtain ⟨value, hValue⟩ :=
    qInputWordWritten hp hX hFrame ho hFinished hSpec slot.1 slot.2.1
  have hMem : X.MemWrites (.async tensor (.write (.load slot.1.val row byte)))
      {loc, size := 1} [((Value.float .bf16 value).byteAt byte)] := by
    have hByte := hValue ⟨byte, hb⟩
    change X.MemWrites (.async tensor (.write (.load slot.1.val row byte)))
      {loc := spec.sharedLoc slot, size := 1} [((Value.float .bf16 value).byteAt byte)] at hByte
    rwa [hLoc] at hByte
  refine ⟨⟨loc, _, _, _, hMem, ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩, rfl, ?_⟩
  have hIssue : X.MmaIssue i d op acc mask := ⟨_, hQk.decoded⟩
  intro other access data hOther hCover
  exact (pendingQueryOtherWriter hp hX hCuQ hBox hOwner hIssue hAt hWrite hPending
    other access data hOther hCover).elim .inl (.inr ∘ .inr)

/-- An actual QK A byte comes from the selected packed launch row in any prefix. -/
theorem actualQkQueryByteOfSelectedAcquireInPrefix (hFrame : OutputFootprint p X) {batch : Nat}
    {i : EvId} {block : Fin 4} {step : Fin 8} {use d : Nat} {acc : Bool} {mask : List Nat}
    {row k byte : Nat}
    (hQk : QkInstruction X i block step d (qkOperands l i.1 block step use) acc mask)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ i.1/l.block)
    (hHi : i.1/l.block < tilePrefix p (batch+1)*p.heads) (hr : row < 128) (hk : k < 16)
    (hByte : byte < 2) :
    let coords := Epilogue.assignedCoordinates p batch (i.1/l.block)
    let firstQ := p.qOffset batch + 256*coords.1 + 128*(qkStage block).val
    ∃ loc, (qkOperands l i.1 block step use).byteLoc .a (qkByteIndex row k byte) = some loc ∧
      OperandByteSource l X i false (qkByteIndex row k byte) loc
        ((Value.float .bf16 (qkQuery p (firstQ+row) coords.2 (16*step.val+k))).byteAt byte) := by
  let stage := qkStage block
  let plane : Fin 2 := ⟨qkPlane step,by unfold qkPlane; have := step.isLt; omega⟩
  let coords := Epilogue.assignedCoordinates p batch (i.1/l.block)
  let firstQ := p.qOffset batch + 256*coords.1 + 128*stage.val
  let spec := qInputSpec p (64*plane.val) firstQ coords.2
    ⟨.shared,i.1/l.block,qStart l stage+16384*plane.val⟩
    (Output.queryObject l (i.1/l.block) stage) false
  let slot := qkQSlot p step hr hk hByte
  let loc := spec.sharedLoc slot
  let hIssue : X.MmaIssue i d (qkOperands l i.1 block step use) acc mask := ⟨_,hQk.decoded⟩
  obtain ⟨wait,e,he,hWait,hBefore⟩ := hQk.queryAcquire hp hX
  obtain ⟨acquire,phase,_,hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e,he,hWait⟩
  obtain ⟨tensor,hTensor,_,hLoc,hValue⟩ :=
    qkQueryOperandOfObservedAcquireInPrefix hp hX hFrame block step hb hLo hHi
      hr hk hByte acquire hPhase hBefore hIssue
  have hBoxIssue : X.TensorIssue tensor p.qMapAddress spec := hTensor
  have hOwner : tensor.1/l.block = i.1/l.block :=
    ((actualMbarOperand hp hX (Execution.UsesMbar.of_tensor hBoxIssue)).1).symm
  have hBox : QuerySubbox p l X tensor stage plane spec := by
    refine ⟨hBoxIssue,?_,?_,rfl,rfl,rfl,rfl⟩
    · change Output.queryObject l (i.1/l.block) stage = _
      rw [hOwner]
    · change Loc.mk .shared (i.1/l.block) (qStart l stage+16384*plane.val) = _
      rw [hOwner]
  have hWrite : TensorCopy.writeLoc spec slot.1.val row byte = some loc := by
    have hs : TensorTransfer.slotAt spec.descriptor slot.1.val row byte = some slot :=
      TensorCopy.slotAt_self slot
    exact congrArg (Option.map spec.sharedLoc) hs
  refine ⟨loc,hLoc,hValue ?_⟩
  intro other access data hOther hCover
  have hOrder := queryOperandOtherWriter hp hX hBox hOwner hWrite
    (fun _ _ _ hStore hCover _ hShared hCta =>
      stageZeroStagingAfterOperand hp hX hStore hCover hShared hCta hIssue hLoc)
    other access data hOther hCover
  exact hOrder.elim .inl (.inr ∘ .inr)

end PTX.Kernels.TmlFa4Fwd.Safety
