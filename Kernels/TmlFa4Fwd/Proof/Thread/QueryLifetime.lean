-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Lemmas.Order.GuardOrder
import Lemmas.Order.DependencyWitness
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy
open TmlFa4Fwd.Mma (qkIssueEvent initialQkBlock qkOperands qkInputByteLoc qkByteIndex)

private theorem queryWaitResumesMma {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {wait mma : EvId} {stage : Fin 2} {e : Event} (he : X.get wait = some e)
    (hKind : e.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta)
    (hBefore : TraceBefore X wait mma) : Resumes kernel X wait mma := by
  obtain ⟨site, kind⟩ := e
  change kind = _ at hKind
  subst kind
  obtain ⟨next, hSpin⟩ := actualCanonicalPoll hX he
  exact Resumes.of_spin he hSpin hBefore.1 hBefore.2.1 hBefore.2.2

/-- Each initial query acquire is a dependency of an active CTA's correction exit. -/
theorem queryAcquireEnablesExit
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat}
    (hGrid : cta < l.grid) (hWork : cta < tilePrefix p p.batch * p.heads)
    (hExit : CtaExited l X cta) (stage : Fin 2) :
    ∃ wait event finish, wait.1 / l.block = cta ∧ X.get wait = some event ∧
      event.kind = .wait (Output.queryObject l (wait.1 / l.block) stage) 0 true true .cta ∧
      OwnerExit l X cta finish ∧
      Relation.TransGen (DepStep l kernel X) (.thread wait, true) (.thread finish, false) := by
  obtain ⟨commit, s, rank, outWait, outScope, finish, hCommit, hOwner, hTarget,
    hNotified, hOutput, hExitStep, hFinish⟩ :=
    terminalOutputObservedBeforeExit hp hX hGrid hWork hExit
  obtain ⟨base, hBank⟩ := initialCanonicalQkIssuesBeforeSecondOutputCommit hp hX hCommit stage
  let mma : EvId := (commit.1, base + (0 : Fin 8).val)
  obtain ⟨_, hGet, hMmaBefore, _, _, _⟩ := hBank 0
  change X.get mma = some (qkIssueEvent l commit.1 (initialQkBlock stage) 0 0) at hGet
  have hMma := Mma.initialQueryFragmentOfIssue (stage := stage) 0 0 hGet
  obtain ⟨qWait, event, hWait, hKind, hQBefore⟩ := hMma.acquire hp hX
  have hCta : qWait.1 / l.block = cta := by
    rw [hQBefore.1]
    exact hOwner
  let readRef : Ref := .async mma (.mmaRead false (qkByteIndex 0 0 0))
  have hIssue : X.MmaIssue mma _ (qkOperands l commit.1 (initialQkBlock stage) 0 0) _ _ :=
    ⟨_, hGet⟩
  have hTracks : TracksMma X mma commit := ⟨rfl, hMmaBefore.2.1, .inl ⟨_, _, _, _, hIssue⟩,
    s, hCommit.issued⟩
  have hDone := (hX.tcCommit commit rank hNotified).2 mma hTracks
  obtain ⟨operands, hOperands⟩ := Option.isSome_iff_exists.mp (hX.tma.2.1.2 mma hDone)
  have hByte := qkInputByteLoc l commit.1 (initialQkBlock stage) 0 0 .a
    (row := 0) (k := 0) (byte := 0) (by decide) (by decide) (by decide)
  obtain ⟨value, hRead, _⟩ := hX.tma.2.1.mma_read_exists (isB := false) hIssue hOperands hByte
  have hReadPresent : X.RefPresent readRef := ⟨_, value, hRead⟩
  have hIssueToRead : DepStep l kernel X (.thread mma, false) (readRef, false) :=
    .inr (.inl ⟨rfl, rfl, mma, _, rfl, rfl, ⟨_, hGet⟩, hReadPresent, trivial⟩)
  have hReadToDone : DepStep l kernel X (readRef, true) (.async mma .mmaDone, false) :=
    DepStep.stage (.inr ⟨rfl, rfl, rfl, hReadPresent, hDone⟩)
  have hDoneToNotify : DepStep l kernel X (.async mma .mmaDone, true)
      (.async commit (.tcNotify rank), false) :=
    DepStep.stage (.inr ⟨rfl, rfl, hTracks, hDone, hNotified⟩)
  have hOutWitness : Witness l X (.async commit (.tcNotify rank)) outWait :=
    Witness.of_mbarObserved (mbarObserved_of_waitObserves hX.tma.2.2.1 hNotified hOutput)
  have hResumes := queryWaitResumesMma hX hWait hKind hQBefore
  have hStart := Relation.TransGen.single (DepStep.of_resumes l hResumes)
  have hPath := hStart.tail hIssueToRead |>.tail (DepStep.node hReadPresent)
    |>.tail hReadToDone |>.tail (DepStep.node hDone) |>.tail hDoneToNotify
    |>.tail (DepStep.of_witness l hOutWitness) |>.tail (DepStep.of_resumes l hExitStep)
  exact ⟨qWait, event, finish, hCta, hWait, hKind, hFinish, hPath⟩

end PTX.Kernels.TmlFa4Fwd.Thread
