-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
public import Kernels.TmlFa4Fwd.Proof.LoaderQueryIssueOrigin
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.MmaQkResult
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma

/-- Each query acquire observes one actual input issue for each of the two physical planes. -/
theorem QueryAcquire.observedSubbox {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {stage : Fin 2} {phase : Nat} (hWait : QueryAcquire l X wait stage)
    (hPhase : QueryAcquirePhase l X wait stage phase) (plane : Fin 2) :
    ∃ tensor spec, tensor.1 / l.block = wait.1 / l.block ∧
      Loader.QuerySubbox p l X tensor stage plane spec ∧
      QueryNotifyPhase l X tensor stage phase := by
  obtain ⟨_, a, b, hNe, ha, hb, _⟩ := hWait.hasTransactionPair hp hX hPhase
  obtain ⟨hA, ⟨planeA, specA, hBoxA⟩, hNoteA, _⟩ := ha
  obtain ⟨hB, ⟨planeB, specB, hBoxB⟩, hNoteB, _⟩ := hb
  have hPlanes : planeA ≠ planeB := by
    intro h
    subst planeB
    exact hNe (Loader.querySubboxUnique hp hX (hA.trans hB.symm) hBoxA hBoxB)
  have hEither : plane = planeA ∨ plane = planeB := by
    fin_cases plane <;> fin_cases planeA <;> fin_cases planeB <;>
      first | decide | exact (hPlanes rfl).elim
  rcases hEither with rfl | rfl
  · exact ⟨a, specA, hA, hBoxA, hNoteA⟩
  · exact ⟨b, specB, hB, hBoxB, hNoteB⟩

private def queryPlane (step : Fin 8) : Fin 2 :=
  ⟨qkPlane step, by unfold qkPlane; have := step.isLt; omega⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- The actual initial fragment identifies the query acquire and the generation it observed. -/
theorem initialQueryAcquirePhase (hX : Consistent l kernel Assumptions.all m X) {stage : Fin 2}
    {mma : EvId} (hIssue : Thread.Mma.InitialQueryFragment X stage mma) :
    ∃ wait phase, QueryAcquire l X wait stage ∧ QueryAcquirePhase l X wait stage phase ∧
      TraceBefore X wait mma := by
  obtain ⟨wait, e, he, hKind, hOrder⟩ := hIssue.acquire hp hX
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e, he, hKind⟩
  exact ⟨wait, phase, hAcquire, hPhase, hOrder⟩

/-- An observed query acquire locates the real writer of a QK query byte and fixes its value.
The other shared writes still need to be ordered outside this byte's use interval. -/
theorem qkQueryOperandOfObservedAcquireInPrefix (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch : Nat} {wait mma : EvId} (block : Fin 4) (step : Fin 8)
    {use dest : Nat} {accum : Bool} {mask : List Nat} {row k byte : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ mma.1 / l.block)
    (hHi : mma.1 / l.block < tilePrefix p (batch + 1) * p.heads) (hr : row < 128) (hk : k < 16)
    (hByte : byte < 2) (hAcquire : QueryAcquire l X wait (qkStage block)) {phase : Nat}
    (hPhase : QueryAcquirePhase l X wait (qkStage block) phase) (hEarlier : TraceBefore X wait mma)
    (hIssue : X.MmaIssue mma dest (qkOperands l mma.1 block step use) accum mask) :
    let coords := Epilogue.assignedCoordinates p batch (mma.1 / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * (qkStage block).val
    let spec := qInputSpec p (64 * qkPlane step) firstQ coords.2
      ⟨.shared, mma.1 / l.block, qStart l (qkStage block) + 16384 * qkPlane step⟩
      (Output.queryObject l (mma.1 / l.block) (qkStage block)) false
    let slot := qkQSlot p step hr hk hByte
    let loc := spec.sharedLoc slot
    ∃ tensor, X.TensorIssue tensor p.qMapAddress spec ∧
      QueryNotifyPhase l X tensor (qkStage block) phase ∧
      (qkOperands l mma.1 block step use).byteLoc .a (qkByteIndex row k byte) = some loc ∧
      ((∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
        other = .async tensor (.write (.load slot.1.val row byte)) ∨
        modelCausality l X loc other (.async tensor (.write (.load slot.1.val row byte))) ∨
        modelCausality l X loc (.async mma (.mmaRead false (qkByteIndex row k byte))) other) →
        OperandByteSource l X mma false (qkByteIndex row k byte) loc
          ((Value.float .bf16 (qkQuery p (firstQ + row) coords.2
            (16 * step.val + k))).byteAt byte)) := by
  dsimp only
  let stage := qkStage block
  let coords := Epilogue.assignedCoordinates p batch (mma.1 / l.block)
  let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
  obtain ⟨tensor, spec, hCta, hBox, hNotify⟩ :=
    hAcquire.observedSubbox hp hX hPhase (queryPlane step)
  have hOwner : tensor.1 / l.block = mma.1 / l.block := by simpa only [hEarlier.1] using hCta
  have hSpec := Loader.querySubboxCoordinatesInPrefix hp hX hb (hOwner.symm ▸ hLo)
    (hOwner.symm ▸ hHi) (fun w a bytes loc hw ha hs => by
      rcases hFrame w a bytes loc hw ha hs with hO | ⟨q, hq, head, hh, j, hj, rfl⟩
      · exact .inl hO
      · exact .inr (lseByte_in hq hh hj)) hBox
  rw [hOwner] at hSpec
  have hh : coords.2 < p.heads := (Epilogue.assignedCoordinates_valid hp hLo hHi).2
  have hTensor := hBox.1
  rw [hSpec] at hTensor
  refine ⟨tensor,hTensor,hNotify,?_,?_⟩
  · exact qkQInputSlot hp mma.1 block step use firstQ coords.2
      (Output.queryObject l (mma.1 / l.block) stage) false hr hk hByte
  · intro hOther
    have hSource := qkQueryOperandSource hp hX hFrame block step
      (absoluteRow := firstQ) hh hr hk hByte hAcquire hPhase hNotify hEarlier hIssue
    dsimp only at hSource
    rw [hEarlier.1] at hSource
    simpa only [qkQuery, qkQSlotLogicalColumn] using hSource hTensor hOther

/-- An observed query acquire locates the real writer of a QK query byte and fixes its value.
The other shared writes still need to be ordered outside this byte's use interval. -/
theorem qkQueryOperandOfObservedAcquire (hX : Consistent l kernel Assumptions.all m X)
    (_hComplete : Complete l X) (hFrame : OutputFootprint p X) {batch : Nat} {wait mma : EvId}
    (block : Fin 4) (step : Fin 8) {use dest : Nat} {accum : Bool} {mask : List Nat}
    {row k byte : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ mma.1 / l.block)
    (hHi : mma.1 / l.block < tilePrefix p (batch + 1) * p.heads) (hr : row < 128) (hk : k < 16)
    (hByte : byte < 2) (hAcquire : QueryAcquire l X wait (qkStage block)) {phase : Nat}
    (hPhase : QueryAcquirePhase l X wait (qkStage block) phase) (hEarlier : TraceBefore X wait mma)
    (hIssue : X.MmaIssue mma dest (qkOperands l mma.1 block step use) accum mask) :
    let coords := Epilogue.assignedCoordinates p batch (mma.1 / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * (qkStage block).val
    let spec := qInputSpec p (64 * qkPlane step) firstQ coords.2
      ⟨.shared, mma.1 / l.block, qStart l (qkStage block) + 16384 * qkPlane step⟩
      (Output.queryObject l (mma.1 / l.block) (qkStage block)) false
    let slot := qkQSlot p step hr hk hByte
    let loc := spec.sharedLoc slot
    ∃ tensor, X.TensorIssue tensor p.qMapAddress spec ∧
      QueryNotifyPhase l X tensor (qkStage block) phase ∧
      (qkOperands l mma.1 block step use).byteLoc .a (qkByteIndex row k byte) = some loc ∧
      ((∀ other access bytes, X.MemWrites other access bytes → access.Covers loc →
        other = .async tensor (.write (.load slot.1.val row byte)) ∨
        modelCausality l X loc other (.async tensor (.write (.load slot.1.val row byte))) ∨
        modelCausality l X loc (.async mma (.mmaRead false (qkByteIndex row k byte))) other) →
        OperandByteSource l X mma false (qkByteIndex row k byte) loc
          ((Value.float .bf16 (qkQuery p (firstQ + row) coords.2
            (16 * step.val + k))).byteAt byte)) := by
  exact qkQueryOperandOfObservedAcquireInPrefix hp hX hFrame block step hb hLo hHi hr hk hByte
    hAcquire hPhase hEarlier hIssue

end PTX.Kernels.TmlFa4Fwd.Protocol
