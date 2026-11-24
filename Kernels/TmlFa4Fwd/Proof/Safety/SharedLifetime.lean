-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.SharedOwnership
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputDrain
public import Lemmas.Kernel.SharedLifetime
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryLifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasIssueFinished
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreNotificationLifetime
public import Kernels.TmlFa4Fwd.Proof.Thread.CommitDestination
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheReleaseLifetime
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryReturnLifetime
public import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCommitTargets
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryReleaseOnce

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A synchronous shared-memory user finishes before its owner CTA exits. -/
theorem sharedThreadFinished (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {owner : Nat} (hUse : SharedUse l X (.thread i) owner) (hExit : CtaExited l X owner)
    :
    SharedFinished l kernel Assumptions.all X (.thread i) owner := by
  have hOwner := sharedUseOwnsShared hp hX hUse
  rcases hUse with ⟨⟨e, he⟩, ⟨a, w, hAccess, _, _⟩ | ⟨_, _, hAction⟩⟩ |
    ⟨j, s, hEq, hi, _⟩ | ⟨_, _, _, _, _, _, hEq, _⟩ |
    ⟨_, _, _, hEq, _⟩ | ⟨_, _, hEq, _⟩
  · exact SharedFinished.of_access hX.outside hAccess hOwner.symm hExit
  · exact SharedFinished.of_thread hX.outside he (by
      rintro _ rfl
      simp [AsyncCopy.objectAction, he] at hAction) hOwner.symm hExit
  · cases hEq
    obtain ⟨_, he⟩ := hi
    exact SharedFinished.of_thread hX.outside he (by rintro _ h; cases h) hOwner.symm hExit
  all_goals cases hEq

/-- A CTA cannot exit while one of its MMAs still uses its shared operands. -/
theorem sharedMmaFinished (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {i : EvId} {dst : Nat} {s : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s accum mask)
    (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i .mmaDone) (i.1 / l.block) :=
  Thread.mmaFinishedAtExitOfWork hp hX hi (mmaHasScheduledTile hp hX hCuQ hi) hExit

/-- A performed operand byte read precedes its MMA completion and the observing correction exit. -/
theorem sharedMmaReadFinished (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {i : EvId} {dst index : Nat} {s : TcMma.OperandSpec}
    {accum isB : Bool} {mask : List Nat} (hi : X.MmaIssue i dst s accum mask)
    (hByte : X.AsyncPresent i (.mmaRead isB index)) (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.mmaRead isB index)) (i.1 / l.block) := by
  have hDone := sharedMmaFinished hp hX hCuQ hi hExit
  exact SharedFinished.of_stage (j := i) (q := .mmaDone) hByte
    (.inr ⟨rfl, rfl, rfl, hByte, hDone.1⟩) hDone

/-- Finishing these stages requires the loader and commit notification histories. -/
private def LoaderOrCommitStage : AsyncCopy.Part → Prop
  | .write .copy | .arriveOn | .notify .load | .tcNotify _ => True
  | _ => False

private theorem sharedAsyncObjectStage {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {part : AsyncCopy.Part} {object : Loc} {act : MBarrier.Action}
    (ha : AsyncCopy.objectAction X X.async object (.async i part) = some act) :
    LoaderOrCommitStage part := by
  obtain ⟨r, hr, hId⟩ := (hX.tma.2.2.1 object).2.2 (.async i part) act ha
  cases AsyncCopy.record_source hX.tma.2.2.1 hr with
  | init h _ _ | inval h _ _ | arrive h _ _ | wait h _ _ | increment h _ _ =>
    rw [h] at hId
    cases hId
  | tensor h _ _ _ | arriveOn h _ _ _ _ | commit h _ _ _ =>
    rw [h] at hId
    obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hId
    trivial
  | bulk _ he hCompletion _ _ =>
    rw [(actualCopyShape hX ⟨_,he⟩).completion] at hCompletion
    cases hCompletion
  | clc _ he _ _ _ => exact (noClcIssue hX ⟨_, he⟩).elim

private theorem sharedAsyncAccessStage (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {part : AsyncCopy.Part} {a : Acc} (hFoot : X.AsyncFootprint i part a)
    (hSpace : a.loc.space = .shared) (hPresent : X.AsyncPresent i part)
    (hExit : CtaExited l X (i.1/l.block)) :
    (LoaderOrCommitStage part ∨ ∃ x y byte, part = .write (.load x y byte)) ∨
      SharedFinished l kernel Assumptions.all X (.async i part) (i.1/l.block) := by
  cases part <;> try (exact False.elim hFoot)
  case mmaRead isB index =>
    obtain ⟨_, hRead⟩ := hFoot
    obtain ⟨_, _, _, _, _, hi, _⟩ := Thread.mmaSharedFootprintIssue hX hRead
    exact .inr (sharedMmaReadFinished hp hX hCuQ hi hPresent hExit)
  case readCopy =>
    rcases hFoot with ⟨s, hi, rfl⟩ | hPrefetch
    · rw [(actualCopyShape hX hi).srcGlobal] at hSpace
      cases hSpace
    · exact (Thread.noBulkPrefetch hX hPrefetch).elim
  case readStore x y k =>
    obtain ⟨s, address, hi, _, _⟩ := hFoot
    exact .inr (Protocol.Output.storeReadFinished hp hX hi hPresent hExit)
  case readLoad x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [Execution.tensor_readLoc_global hl] at hSpace
    cases hSpace
  case readPrefetch x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [TensorTransfer.sourceLoc_global hl] at hSpace
    cases hSpace
  case writeCopy => exact .inl (.inl trivial)
  case writeElem index =>
    obtain ⟨s, hi, hAt⟩ := hFoot
    simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, (actualCopyShape hX hi).whole] at hAt
  case writeStore x y k =>
    obtain ⟨_, _, _, hl, _⟩ := hFoot
    rw [Execution.store_writeLoc_global hl] at hSpace
    cases hSpace
  case writeLoad x y k => exact .inl (.inr ⟨x,y,k,rfl⟩)
  case writeCta owner =>
    obtain ⟨_, _, hi, _, _⟩ := hFoot
    exact (noClcIssue hX hi).elim
  case oldElem index =>
    obtain ⟨s, red, hi, hw, _⟩ := hFoot
    rw [(actualCopyShape hX hi).whole] at hw
    cases hw
  case oldStore x y k =>
    obtain ⟨_, _, _, _, hl, _⟩ := hFoot
    rw [Execution.store_writeLoc_global hl] at hSpace
    cases hSpace

private theorem classifySharedLifetimeFailure (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    (h : SharedLifetimeUnsafe l kernel Assumptions.all X) :
    ∃ i part, (LoaderOrCommitStage part ∨ ∃ x y byte, part = .write (.load x y byte)) ∧
      SharedUse l X (.async i part) (i.1/l.block) ∧ CtaExited l X (i.1/l.block) ∧
      ¬ SharedFinished l kernel Assumptions.all X (.async i part) (i.1/l.block) := by
  obtain ⟨ref, owner, hUse, hUnsafe⟩ := h
  have hOwner := sharedUseOwnsShared hp hX hUse
  rcases hUnsafe with ⟨hPeer, _⟩ | ⟨hExit, hPending⟩
  · exact (hPeer hOwner).elim
  subst owner
  cases ref with
  | thread i => exact (hPending (sharedThreadFinished hp hX hUse hExit)).elim
  | async i part =>
    refine ⟨i, part, ?_, hUse, hExit, hPending⟩
    rcases hUse with ⟨hPresent, ⟨_, _, hIntent, hSpace, _⟩ | ⟨_, _, hAction⟩⟩ |
      ⟨_, _, hEq, _⟩ | ⟨_, _, _, _, _, _, hEq, _⟩ |
      ⟨_, address, s, hEq, hi, _⟩ | ⟨_, _, hEq, hFinal, hUses⟩
    · exact (sharedAsyncAccessStage hp hX hCuQ hIntent.2 hSpace hPresent hExit)
        |>.resolve_right hPending
    · exact .inl (sharedAsyncObjectStage hX hAction)
    · cases hEq
    · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
      exact .inr ⟨_,_,_,rfl⟩
    · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
      exact (hPending (Protocol.Output.storeReadsFinished hp hX hi hExit)).elim
    · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
      cases part <;> try exact False.elim hUses
      case writeCopy | notifyLoad | tcNotify => exact .inl (by simp [LoaderOrCommitStage])
      case notifyCopy =>
        obtain ⟨s, _, hi, hc, _⟩ := hUses
        rw [(actualCopyShape hX hi).completion] at hc
        cases hc
      case notifyCta =>
        rcases hFinal with ⟨_, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ |
          ⟨s, targets, _, hi, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
        all_goals first | cases h | exact (noClcIssue hX hi).elim
      case mmaDone =>
        rcases hUses with ⟨dst, s, accum, mask, hi, _⟩ | ⟨s, hi, _⟩
        · exact (hPending (sharedMmaFinished hp hX hCuQ hi hExit)).elim
        · exact (Thread.noTensorCopyOperandIssue hX hi).elim

private theorem inputIssueOfSharedWrite {l : Launch} {X : Execution}
    {i : EvId} {x y k owner : Nat}
    (hUse : SharedUse l X (.async i (.write (.load x y k))) owner) :
    ∃ addr spec, X.TensorIssue i addr spec ∧
      (TensorTransfer.slotAt spec.descriptor x y k).isSome := by
  rcases hUse with ⟨_, ⟨_, _, hIntent, _, _⟩ | ⟨_, _, hAction⟩⟩ |
    ⟨_, _, hEq, _⟩ | ⟨_, addr, spec, _, _, _, hEq, hi, hSlot, _⟩ |
    ⟨_, _, _, hEq, _⟩ | ⟨_, _, hEq, _, hUses⟩
  · obtain ⟨spec, addr, hi, hl, _⟩ := hIntent.2
    obtain ⟨slot, hs, _⟩ := Option.map_eq_some_iff.mp hl
    exact ⟨addr, spec, hi, by simp [hs]⟩
  · cases hAction
  · cases hEq
  · obtain ⟨rfl, hPart⟩ := AsyncCopy.Ref.async.inj hEq
    obtain ⟨rfl, rfl, rfl⟩ := AsyncCopy.Slot.load.inj (AsyncCopy.Part.write.inj hPart)
    exact ⟨addr, spec, hi, hSlot⟩
  · cases hEq
  · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
    exact False.elim hUses

private theorem sharedInputWriteFinishedOfNotify {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr x y k owner : Nat} {spec : TensorCopy.Spec}
    (hi : X.TensorIssue i addr spec) (hSlot : (TensorTransfer.slotAt spec.descriptor x y k).isSome)
    (hDone : SharedFinished l kernel Assumptions.all X (.async i (.notify .load)) owner) :
    SharedFinished l kernel Assumptions.all X (.async i (.write (.load x y k))) owner := by
  obtain ⟨o, hObs, hNotify⟩ := hDone.1
  obtain ⟨⟨_, _, hActual⟩, hCopy, _⟩ := hX.tensor i o hObs
  obtain ⟨_, hEvent⟩ := hi
  rw [hActual] at hEvent
  have hSpec := (Kind.tensorIssue.inj (Event.mk.inj (Option.some.inj hEvent)).2).2
  subst spec
  obtain ⟨slot, hAt⟩ := Option.isSome_iff_exists.mp hSlot
  obtain ⟨value, hWritten⟩ := hCopy.complete hNotify slot
  have hPresent : X.AsyncPresent i (.write (.load x y k)) :=
    ⟨o, slot, value, hObs, hAt, hWritten⟩
  exact SharedFinished.of_stage (j := i) (q := .notify .load) hPresent
    (.inr ⟨rfl, rfl, rfl, rfl, hPresent, o, hObs, hNotify⟩) hDone

private theorem inputIssueOfSharedNotify {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {owner : Nat}
    (hUse : SharedUse l X (.async i (.notify .load)) owner) :
    ∃ address spec, X.TensorIssue i address spec := by
  rcases hUse with ⟨⟨o, hObs, _⟩, _⟩ | ⟨_, _, hEq, _⟩ |
    ⟨_, _, _, _, _, _, hEq, _⟩ | ⟨_, _, _, hEq, _⟩ | ⟨_, _, hEq, _, hStage⟩
  · obtain ⟨⟨address, _, he⟩, _, _⟩ := hX.tensor i o hObs
    exact ⟨address, o.spec, _, he⟩
  · cases hEq
  · cases hEq
  · cases hEq
  · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
    obtain ⟨address, spec, hi, _, _⟩ := hStage
    exact ⟨address, spec, hi⟩

private theorem sharedInputNotifyFinished (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {address : Nat} {spec : TensorCopy.Spec} (hi : X.TensorIssue i address spec)
    (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.notify .load)) (i.1 / l.block) := by
  rcases Loader.tensorInputSubbox hp hX hi with ⟨stage, plane, hBox⟩ | ⟨stage, half, hBox⟩
  · exact Protocol.queryNotificationFinishedAtExit hp hX hCuQ hBox hExit
  · exact Protocol.Bias.biasTensorNotificationFinishedAtExit hp hX hCuQ hBox hExit

/-- Both terminal output commit notifications precede the observing correction exit. -/
theorem terminalOutputNotificationFinishedAtExit (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {spec : TcCommit.Spec} {rank : Fin 16}
    (hCommit : FirstOutputCommit X i spec ∨ SecondOutputCommit X i spec)
    (hTarget : (TcCommit.target spec rank).isSome) (hExit : CtaExited l X (i.1 / l.block)) :
    SharedFinished l kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / l.block) := by
  have hi : X.Commit i spec := hCommit.elim FirstOutputCommit.issued SecondOutputCommit.issued
  obtain ⟨loc, hSingle⟩ := commitTargetSingle hp hX hi
  obtain ⟨_, he⟩ := hi
  have hGrid := NamedBar.cta_lt (PTX.Proof.event_thread_lt hX he)
  have rankZero (r : Fin 16) (h : (TcCommit.target spec r).isSome) : r.val = 0 := by
    by_contra hBad
    rw [hSingle r, ite_eq_right hBad] at h
    cases h
  have finished {other wait exit : EvId} {spec' : TcCommit.Spec} {observed : Fin 16}
      {obj : Loc} {scope : MbarScope} (hEq : other = i) (hc : X.Commit other spec')
      (ht : TcCommit.target spec' observed = some obj) (hNote : observed ∈ X.tcNotified other)
      (hObs : WaitObserves X (.async other (.tcNotify observed)) wait obj true scope)
      (hResumes : Resumes kernel X wait exit) (hOwner : OwnerExit l X (i.1 / l.block) exit) :
      SharedFinished l kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / l.block) := by
    subst other
    obtain ⟨_, he'⟩ := hc
    rw [he] at he'
    obtain rfl := TcKind.commit.inj (Kind.tc.inj (Event.mk.inj (Option.some.inj he')).2)
    have hR : observed = rank := Fin.ext
      ((rankZero observed (by simp [ht])).trans (rankZero rank hTarget).symm)
    subst observed
    exact SharedFinished.of_completedBefore hNote hOwner
      (CompletedBefore.of_before hObs.before (.single (DepStep.of_resumes l hResumes)))
  rcases hCommit with hFirst | hSecond
  · obtain ⟨mma, _, _, _, _, _, _, hLane, _, hMma, _, _⟩ :=
      firstOutputCommitHasQueryFragmentOfPrefix hp hX hFirst
    have hWork := hLane ▸ mmaHasScheduledTile hp hX hCuQ hMma
    obtain ⟨other, found, r, w, scope, exit, hFound, hCta, ht, hNote, hObs, hRes, hOwner⟩ :=
      terminalFirstOutputObservedBeforeExit hp hX hGrid hWork hExit
    have hEq := Thread.Mma.terminalCommitUnique hp hX (.output 0) hCta hFound hFirst
    exact finished hEq hFound.issued ht hNote hObs hRes hOwner
  · obtain ⟨base, hMmas⟩ := initialKeyIssuesWithDescriptorBeforeSecondOutputCommit hp hX hSecond 0
    obtain ⟨_, _, _, _, _, hMma, _, _⟩ := hMmas 0
    have hWork := mmaHasScheduledTile hp hX hCuQ hMma
    obtain ⟨other, found, r, w, scope, exit, hFound, hCta, ht, hNote, hObs, hRes, hOwner⟩ :=
      terminalOutputObservedBeforeExit hp hX hGrid hWork hExit
    have hEq := Thread.Mma.terminalCommitUnique hp hX (.output 1) hCta
      hFound.decoded hSecond.decoded
    exact finished hEq hFound.issued ht hNote hObs hRes hOwner

private theorem commitOfSharedNotify {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {rank : Fin 16} {owner : Nat}
    (hUse : SharedUse l X (.async i (.tcNotify rank)) owner) :
    ∃ spec object, X.Commit i spec ∧ TcCommit.target spec rank = some object := by
  rcases hUse with ⟨hPresent, _⟩ | ⟨_, _, hEq, _⟩ |
    ⟨_, _, _, _, _, _, hEq, _⟩ | ⟨_, _, _, hEq, _⟩ | ⟨_, _, hEq, _, hStage⟩
  · exact (hX.tcCommit i rank hPresent).1
  · cases hEq
  · cases hEq
  · cases hEq
  · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
    obtain ⟨spec, object, hi, ht, _⟩ := hStage
    exact ⟨spec, object, hi, ht⟩

private theorem copyOfSharedWrite {l : Launch} {X : Execution}
    {i : EvId} {owner : Nat} (hUse : SharedUse l X (.async i (.write .copy)) owner) :
    ∃ spec, X.Copy i spec := by
  rcases hUse with ⟨_, ⟨_, _, hIntent, _, _⟩ | ⟨_, _, hAction⟩⟩ |
    ⟨_, _, hEq, _⟩ | ⟨_, _, _, _, _, _, hEq, _⟩ | ⟨_, _, _, hEq, _⟩ |
    ⟨_, _, hEq, _, hStage⟩
  · obtain ⟨spec, hi, _, _⟩ := hIntent.2
    exact ⟨spec, hi⟩
  · cases hAction
  · cases hEq
  · cases hEq
  · cases hEq
  · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
    obtain ⟨spec, hi, _, _⟩ := hStage
    exact ⟨spec, hi⟩

private theorem publicationOfSharedArrival {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {owner : Nat} (hUse : SharedUse l X (.async i .arriveOn) owner) :
    ∃ loc, X.AsyncArrive i loc true := by
  rcases hUse with ⟨hPresent, _⟩ | ⟨_, _, hEq, _⟩ | ⟨_, _, _, _, _, _, hEq, _⟩ |
    ⟨_, _, _, hEq, _⟩ | ⟨_, _, hEq, _, hStage⟩
  · obtain ⟨loc, noinc, hi⟩ := (hX.tma.2.2.2 i hPresent).1
    cases noinc
    · exact (Loader.noIncrementingCopyArrival hX hi).elim
    · exact ⟨loc, hi⟩
  · cases hEq
  · cases hEq
  · cases hEq
  · obtain ⟨rfl, rfl⟩ := AsyncCopy.Ref.async.inj hEq
    exact hStage.elim

/-- Every shared-memory use is local to its CTA and is finished before the owning CTA exits. -/
theorem noSharedLifetimeUnsafe (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) :
    ¬ SharedLifetimeUnsafe l kernel Assumptions.all X := by
  intro hUnsafe
  obtain ⟨i, part, hStage | ⟨x, y, k, rfl⟩, hUse, hExit, hPending⟩ :=
    classifySharedLifetimeFailure hp hX hCuQ hUnsafe
  · apply hPending
    cases part <;> try exact False.elim hStage
    case writeCopy =>
      obtain ⟨_, hi⟩ := copyOfSharedWrite hUse
      exact Protocol.LoaderReady.actualCopyFinishedAtExit hp hX hi hExit
    case arriveOn =>
      obtain ⟨_, hi⟩ := publicationOfSharedArrival hX hUse
      exact Protocol.LoaderReady.actualPublicationFinishedAtExit hp hX hi hExit
    case notifyLoad =>
      obtain ⟨_, _, hi⟩ := inputIssueOfSharedNotify hX hUse
      exact sharedInputNotifyFinished hp hX hCuQ hi hExit
    case tcNotify rank =>
      obtain ⟨spec, _, hi, ht⟩ := commitOfSharedNotify hX hUse
      rcases commitDestination hp hX hi ht with hOut | ⟨stage, hQ⟩ | ⟨stage, hScore⟩ | ⟨slot, hKV⟩
      · exact terminalOutputNotificationFinishedAtExit hp hX hCuQ hOut (by simp [ht]) hExit
      · exact Protocol.queryReturnFinishedAtExit hp hX hCuQ hQ hExit
      · exact Protocol.Scores.scoreNotificationFinishedAtExit hp hX hCuQ hScore hExit
      · exact Protocol.LoaderReady.cacheReleaseFinishedAtExit hp hX hKV hExit
  · obtain ⟨_, _, hi, hSlot⟩ := inputIssueOfSharedWrite hUse
    exact hPending (sharedInputWriteFinishedOfNotify hX hi hSlot
      (sharedInputNotifyFinished hp hX hCuQ hi hExit))

end PTX.Kernels.TmlFa4Fwd.Safety
