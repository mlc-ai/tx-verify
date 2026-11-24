-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.CommitOperandOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
import Lemmas.Tensor.LoadWritten

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy
open Thread (FirstOutputCommit firstOutputAcquireReads firstOutputCommitHasQueryBytesOfPrefix)
open Thread.Correction (FirstOutputAcquire)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A parity-zero Q0 acquire observed both physical planes, including the specified actual
Q0 input issue. Distinct credits must have come from different planes. -/
theorem queryAcquireObservesZeroSubbox {input wait : EvId} {plane : Fin 2} {s : TensorCopy.Spec}
    (hCta : input.1 / l.block = wait.1 / l.block)
    (hBox : Thread.Loader.QuerySubbox p l X input 0 plane s)
    (hWait : ∃ e, X.get wait = some e ∧
      e.kind = .wait (Thread.Output.queryObject l (wait.1 / l.block) 0) 0 true true .cta) :
    QueryAcquire l X wait 0 ∧ ∃ phase, QueryAcquirePhase l X wait 0 phase ∧
      QueryNotifyPhase l X input 0 phase := by
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX hWait
  obtain ⟨_, a, b, hNe, ha, hb, _⟩ := hAcquire.hasTransactionPair hp hX hPhase
  obtain ⟨hA, ⟨planeA, specA, hBoxA⟩, hNoteA, _⟩ := ha
  obtain ⟨hB, ⟨planeB, specB, hBoxB⟩, hNoteB, _⟩ := hb
  have hPlanes : planeA ≠ planeB := by
    intro h
    subst planeB
    exact hNe (Thread.Loader.querySubboxZeroUnique hp hX (hA.trans hB.symm) hBoxA hBoxB)
  have hEither : plane = planeA ∨ plane = planeB := by
    fin_cases plane <;> fin_cases planeA <;> fin_cases planeB <;>
      first | decide | exact (hPlanes rfl).elim
  rcases hEither with h | h
  · subst planeA
    have hEq := Thread.Loader.querySubboxZeroUnique hp hX (hCta.trans hA.symm) hBox hBoxA
    exact ⟨hAcquire, phase, hPhase, hEq.symm ▸ hNoteA⟩
  · subst planeB
    have hEq := Thread.Loader.querySubboxZeroUnique hp hX (hCta.trans hB.symm) hBox hBoxB
    exact ⟨hAcquire, phase, hPhase, hEq.symm ▸ hNoteB⟩

omit hp hX in
private theorem completedQueryWrite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {input mma : EvId} {x y byte index : Nat} {loc : Loc}
    (hInput : ∃ a, X.Intent (.async input (.write (.load x y byte))) a true ∧ a.Covers loc)
    (hPrior : modelCausality l X loc (.async input (.write (.load x y byte)))
      (.async mma (.mmaRead false index))) :
    X.AsyncPresent input (.write (.load x y byte)) := by
  obtain ⟨a, hWrites, _⟩ := hInput
  obtain ⟨_, spec, addr, hIssue, hSlot, _⟩ := hWrites
  obtain ⟨observation, ho, hn⟩ := tensor_notified_of_modelCausality hPrior
  obtain ⟨_, hActual⟩ := (hX.tensor input observation ho).1
  obtain ⟨_, hi⟩ := hIssue
  obtain ⟨_, hq⟩ := hActual
  have hSpec : observation.spec = spec :=
    (Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hq.symm.trans hi)))).2
  have hAt : ∃ slot, TensorTransfer.slotAt observation.spec.descriptor x y byte = some slot := by
    rw [hSpec]
    exact (Option.map_eq_some_iff.mp hSlot).imp (fun _ h => h.1)
  obtain ⟨slot, hs⟩ := hAt
  obtain ⟨value, hv⟩ := (hX.tensor input observation ho).2.1.complete hn slot
  exact ⟨observation, slot, value, ho, hs, hv⟩

/-- The observed output commit carries order at a query byte from its tracked operand read to
the correction store. The issuer supplies the tracked MMA and its preceding query acquire. -/
theorem queryBeforeOutputOfTrackedOperand {input wait writer : EvId} {x y byte : Nat} {loc : Loc}
    {dst : Acc} {bytes : List Byte} (hShared : loc.space = .shared)
    (hInput : ∃ a, X.Intent (.async input (.write (.load x y byte))) a true ∧ a.Covers loc)
    (hWait : FirstOutputAcquire l X wait) (hLater : po X wait writer)
    (hWrite : X.Writes writer dst bytes) (hCover : dst.Covers loc)
    (hPrior : ∀ commit s, FirstOutputCommit X commit s → SameCta l commit.1 wait.1 →
      ∃ mma d op accum mask index, X.MmaIssue mma d op accum mask ∧
        mma.1 = commit.1 ∧ mma.2 < commit.2 ∧ op.byteLoc .a index = some loc ∧
        modelCausality l X loc (.async input (.write (.load x y byte)))
          (.async mma (.mmaRead false index))) :
    X.AsyncPresent input (.write (.load x y byte)) ∧
      ByteCausality l X loc (.async input (.write (.load x y byte))) (.thread writer) := by
  obtain ⟨commit, spec, scope, hCommit, hCta, hRead⟩ := firstOutputAcquireReads hp hX hWait
  obtain ⟨mma, d, op, accum, mask, index, hMma, hLane, hEarlier, hLoc, hOrder⟩ :=
    hPrior commit spec hCommit hCta
  obtain ⟨hObserved, hScope, hActual⟩ :=
    hRead (isB := false) hMma hLane hEarlier hLoc
  exact ⟨completedQueryWrite hX hInput hOrder,
    .commitOperand hShared hInput (.inl ⟨d, op, accum, mask, hMma⟩) hActual (.direct hOrder)
      ⟨scope, hObserved, hScope⟩ hLater
      ⟨dst, .inl ⟨true, .inr (.inl ⟨bytes, hWrite, rfl⟩)⟩, hCover⟩⟩

/-- An actual store following the output acquire is ordered after each overwritten Q0 byte. -/
theorem firstQueryByteBeforeOutputOfPrefix {input wait writer : EvId} {s : TensorCopy.Spec}
    {x y byte offset : Nat} (hOffset : offset < 4) {dst : Acc} {bytes : List Byte}
    (hCta : input.1 / l.block = writer.1 / l.block)
    (hBox : Thread.Loader.QuerySubbox p l X input 0 0 s)
    (hAddr : TensorCopy.writeLoc s x y byte =
      some ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩)
    (hWait : FirstOutputAcquire l X wait) (hLater : po X wait writer)
    (hWrite : X.Writes writer dst bytes)
    (hCover : dst.Covers ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩) :
    X.AsyncPresent input (.write (.load x y byte)) ∧
      ByteCausality l X ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩
        (.async input (.write (.load x y byte))) (.thread writer) := by
  let loc : Loc := ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩
  have hIntent : X.Intent (.async input (.write (.load x y byte))) {loc, size := 1} true :=
    ⟨rfl, s, _, hBox.1, hAddr, rfl⟩
  apply queryBeforeOutputOfTrackedOperand hp hX rfl
    ⟨_, hIntent, ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩ hWait hLater hWrite hCover
  intro commit spec hCommit hSame
  obtain ⟨mma, qWait, qPoll, d, op, accum, mask, hLane, hBefore, hMma, hPoll, hKind,
      hTrace, hRead⟩ := firstOutputCommitHasQueryBytesOfPrefix hp hX hCommit
  have hOwner : mma.1 / l.block = writer.1 / l.block := by
    rw [hLane, hSame.2.2, hLater.1]
  have hQueryOwner : qWait.1 / l.block = writer.1 / l.block := by
    rw [hTrace.1]
    exact hOwner
  have hQueryCta := hCta.trans hQueryOwner.symm
  have hQueryWait : ∃ e, X.get qWait = some e ∧
      e.kind = .wait (Thread.Output.queryObject l (qWait.1 / l.block) 0) 0 true true .cta :=
    ⟨qPoll, hPoll, by simpa only [hTrace.1] using hKind⟩
  obtain ⟨hAcquire, phase, hPhase, hNotify⟩ :=
    queryAcquireObservesZeroSubbox hp hX hQueryCta hBox hQueryWait
  have hObject : s.mbar = Thread.Output.queryObject l (qWait.1 / l.block) 0 := by
    simpa only [hQueryCta] using hBox.2.1
  have hRead' : op.byteLoc .a offset = some loc := by
    simpa [loc, hOwner] using hRead offset hOffset
  exact ⟨mma, d, op, accum, mask, offset, hMma, hLane, hBefore, hRead',
    queryBeforeOperand hp hX hBox.1 hObject hAcquire hPhase hNotify hTrace hAddr hMma hRead'⟩

/-- The four-byte Q/O handoff, specialized to a completed execution. -/
theorem firstQueryByteBeforeOutput (_hDone : Complete l X) {input wait writer : EvId}
    {s : TensorCopy.Spec} {x y byte offset : Nat} (hOffset : offset < 4) {dst : Acc}
    {bytes : List Byte} (hCta : input.1 / l.block = writer.1 / l.block)
    (hBox : Thread.Loader.QuerySubbox p l X input 0 0 s)
    (hAddr : TensorCopy.writeLoc s x y byte =
      some ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩)
    (hWait : FirstOutputAcquire l X wait) (hLater : po X wait writer)
    (hWrite : X.Writes writer dst bytes)
    (hCover : dst.Covers ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩) :
    X.AsyncPresent input (.write (.load x y byte)) ∧
      ByteCausality l X ⟨.shared, writer.1 / l.block, l.sharedBase + 3072 + offset⟩
        (.async input (.write (.load x y byte))) (.thread writer) :=
  firstQueryByteBeforeOutputOfPrefix hp hX hOffset hCta hBox hAddr hWait hLater hWrite hCover

end PTX.Kernels.TmlFa4Fwd.Protocol
