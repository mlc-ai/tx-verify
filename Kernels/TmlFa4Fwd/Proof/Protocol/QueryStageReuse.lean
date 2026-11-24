-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryOutputHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess)
open Thread.Correction (FirstOutputAcquire)

private theorem observesQueryPlane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input wait : EvId} {stage plane : Fin 2} {s : TensorCopy.Spec}
    (hCta : input.1 / l.block = wait.1 / l.block)
    (hBox : Loader.QuerySubbox p l X input stage plane s)
    (hWait : ∃ e, X.get wait = some e ∧
      e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta) :
    QueryAcquire l X wait stage ∧ ∃ phase, QueryAcquirePhase l X wait stage phase ∧
      QueryNotifyPhase l X input stage phase := by
  obtain ⟨hAcquire, phase, _, hPhase⟩ := queryAcquirePhaseOfZero hp hX hWait
  obtain ⟨_, a, b, hNe, ha, hb, _⟩ := hAcquire.hasTransactionPair hp hX hPhase
  obtain ⟨hA, ⟨planeA, specA, hBoxA⟩, hNoteA, _⟩ := ha
  obtain ⟨hB, ⟨planeB, specB, hBoxB⟩, hNoteB, _⟩ := hb
  have hPlanes : planeA ≠ planeB := by
    intro h
    subst planeB
    exact hNe (Loader.querySubboxUnique hp hX (hA.trans hB.symm) hBoxA hBoxB)
  have hEither : plane = planeA ∨ plane = planeB := by
    fin_cases plane <;> fin_cases planeA <;> fin_cases planeB <;>
      first | decide | exact (hPlanes rfl).elim
  rcases hEither with h | h
  · subst planeA
    have hEq := Loader.querySubboxUnique hp hX (hCta.trans hA.symm) hBox hBoxA
    exact ⟨hAcquire, phase, hPhase, hEq.symm ▸ hNoteA⟩
  · subst planeB
    have hEq := Loader.querySubboxUnique hp hX (hCta.trans hB.symm) hBox hBoxB
    exact ⟨hAcquire, phase, hPhase, hEq.symm ▸ hNoteB⟩

/-- Once the observed terminal commit's actual query bank is identified, every overlapping
query intent is written and ordered before the correction element using that bank. No warp
exit, completed execution, or pre-existing write effect is needed. -/
theorem queryIntentBeforeCorrectionOfBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input wait writer : EvId} {s : TensorCopy.Spec} {loc : Loc} {bytes : List Byte}
    {qStage plane correctionStage : Fin 2} {subbox : Fin 4} {qx qy qbyte x row : Nat}
    (hBox : Loader.QuerySubbox p l X input qStage plane s)
    (hQuery : TensorCopy.writeLoc s qx qy qbyte = some loc)
    (hWait : FirstOutputAcquire l X wait) (hLater : po X wait writer)
    (hWrite : X.Writes writer (outputElementAccess l writer.1 correctionStage subbox x row) bytes)
    (hx : x < 32) (hy : row < 128)
    (hCover : (outputElementAccess l writer.1 correctionStage subbox x row).Covers loc)
    (hBank : ∀ commit s, FirstOutputCommit X commit s → QueryBankBeforeOutput l X commit qStage) :
    X.AsyncPresent input (.write (.load qx qy qbyte)) ∧
      ByteCausality l X loc (.async input (.write (.load qx qy qbyte))) (.thread writer) := by
  obtain ⟨rfl, rfl, _, hCta, offset, hOffset, hLoc⟩ :=
    querySubboxOfCorrectionOverlap hBox hQuery hx hy hCover
  have hSpace : loc.space = .shared := by rw [hLoc]; rfl
  have hInput : X.Intent (.async input (.write (.load qx qy qbyte))) {loc, size := 1} true :=
    ⟨rfl, s, _, hBox.1, hQuery, rfl⟩
  apply queryBeforeOutputOfTrackedOperand hp hX hSpace
    ⟨_, hInput, ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩ hWait hLater hWrite hCover
  intro commit spec hCommit hSame
  obtain ⟨qWait, poll, hPoll, hKind, hMmas⟩ := hBank commit spec hCommit
  let step := correctionQueryFragment subbox x offset hx hOffset
  obtain ⟨mma, d, op, accum, mask, hMma, hLane, hBefore, hTrace, hBankOp⟩ := hMmas step
  have hOwner : mma.1 / l.block = writer.1 / l.block := by
    rw [hLane, hSame.2.2, hLater.1]
  have hQueryOwner : qWait.1 / l.block = writer.1 / l.block := by
    rw [hTrace.1]
    exact hOwner
  have hQueryCta := hCta.trans hQueryOwner.symm
  obtain ⟨hAcquire, phase, hPhase, hNotify⟩ :=
    observesQueryPlane hp hX hQueryCta hBox ⟨poll, hPoll, hKind⟩
  have hObject : s.mbar = Output.queryObject l (qWait.1 / l.block) (correctionQueryStage subbox) :=
    hBox.2.1.trans (congrArg (fun cta => Output.queryObject l cta _) hQueryCta)
  have hRead := (correctionQueryByteLoc hp hOwner hx hy hOffset hBankOp).trans
    (congrArg some hLoc.symm)
  exact ⟨mma, d, op, accum, mask, _, hMma, hLane, hBefore, hRead,
    queryBeforeOperand hp hX hBox.1 hObject hAcquire hPhase hNotify hTrace hQuery hMma hRead⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
