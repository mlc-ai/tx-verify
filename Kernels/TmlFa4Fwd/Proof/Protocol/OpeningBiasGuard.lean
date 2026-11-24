-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondQueryProgress
import Kernels.TmlFa4Fwd.Proof.Thread.FirstQueryReadyOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryStartProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.MBarrier PTX.Proof PTX.AsyncCopy Thread.Loader Prologue Epilogue

/-- A loader that still waits for its opening Bias buffer sees the initial empty phase.
A return would require a softmax observation of a Bias expectation by the same loader warp. -/
theorem openingBiasEmptyPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hBlocked : OpeningBiasBlocked l X g) :
    let log := X.objects (biasEmptyObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  obtain ⟨hInit,hRecord⟩ := openingBiasEmptyInitialized hp hMax (NamedBar.cta_lt hg)
  apply Protocol.Loader.releasePhaseZeroOfPositiveInit hMax.1
    (show validCount 4 by decide) hInit hRecord
  intro r hr hCounter
  obtain ⟨issue,_,hIssue,_,_,_,_⟩ := Thread.Softmax.biasEmptyUpdate hp hMax.1 0 hr hCounter
  obtain ⟨_,_,_,_,hReady,_,hOk,hObserved,_,_⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hMax.1 0 (e := issue) hIssue
  obtain ⟨expect,hExpect,_,_⟩ := biasObservedExpectation hp hMax.1 0 hReady hOk hObserved
  exact noBiasExpectationAtOpeningPoll hp hMax.1 hg hw hBlocked 0 (issue := expect) hExpect

/-- A loader lane at the opening stage-one Bias guard can acquire the initial empty buffer. -/
theorem openingSecondBiasEmptyPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hBlocked : OpeningSecondBiasBlocked l X g) :
    let log := X.objects (biasEmptyObject l (g/l.block) 1)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  obtain ⟨hInit,hRecord⟩ :=
    openingBiasEmptyInitializedAtStage hp hMax (NamedBar.cta_lt hg) 1
  apply Protocol.Loader.releasePhaseZeroOfPositiveInit hMax.1
    (show validCount 4 by decide) hInit hRecord
  intro r hr hCounter
  obtain ⟨issue,_,hIssue,_,_,_,_⟩ := Thread.Softmax.biasEmptyUpdate hp hMax.1 1 hr hCounter
  obtain ⟨_,_,_,_,hReady,_,hOk,hObserved,_,_⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hMax.1 1 (e := issue) hIssue
  obtain ⟨expect,hExpect,_,_⟩ := biasObservedExpectation hp hMax.1 1 hReady hOk hObserved
  exact noSecondBiasExpectationAtOpeningPoll hp hMax.1 hg hw hBlocked (issue := expect) hExpect

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier PTX.Proof PTX.AsyncCopy Thread.Loader Prologue Epilogue

/-- A loader lane still at its first query guard sees the initial Q0 empty phase. -/
theorem openingFirstQueryEmptyPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hBlocked : OpeningFirstQueryBlocked l X g) :
    let log := X.objects (queryEmptyObject l (g/l.block) 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  obtain ⟨hInit,hRecord⟩ := TmlFa4Fwd.Loader.firstQueryEmptyInitializedOfMaximal hp hMax
    (NamedBar.cta_lt hg)
  apply releasePhaseZeroOfInitialized hMax.1 hInit hRecord
  intro r hr hCounter
  obtain ⟨_,_,hAt,hAction,hOk⟩ :=
    TmlFa4Fwd.Loader.firstQueryPollOfEmptyUpdate hp hMax.1 hr hCounter
  obtain ⟨_,_,_,hCta,hBox⟩ := successfulQueryPollHasSubbox hp hMax.1 hAt hAction hOk
  exact noQuerySubboxAtOpeningPoll hp hMax.1 hg hw hBlocked hCta hBox

/-- A loader lane at the opening Q1 guard can acquire the initial empty buffer. -/
theorem openingSecondQueryEmptyPhaseForBlockedLane
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hBlocked : OpeningSecondQueryBlocked l X g) :
    let log := X.objects (secondQueryEmpty l (g/l.block))
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  apply releasePhaseZeroOfNoUpdates hp hMax (NamedBar.cta_lt hg) .secondQuery
  intro r hr hUpdate
  obtain ⟨read,hRead,hSuccess⟩ :=
    TmlFa4Fwd.Loader.secondQueryReturnRequiresAcquisition hp hMax.1 hr hUpdate
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hRead
  obtain ⟨_,q,_,hAction,_,_⟩ := (X.objects_checked hMax.1 _).okPoll hi hSuccess
  have hZero : q = 0 := by
    cases record_source hMax.1.tma.2.2.1 hRead with
    | wait _ he ha =>
      have hSame := (Action.pollParity.inj (hAction.symm.trans ha)).1
      exact hSame.trans (secondQueryReadyPollParity hp hMax.1 he rfl)
    | init _ _ ha | inval _ _ ha | arrive _ _ ha | increment _ _ ha
    | tensor _ _ _ ha | commit _ _ _ ha | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha
    | clc _ _ _ _ ha => rw [hAction] at ha; cases ha
  subst q
  obtain ⟨_,_,_,hCta,hBox⟩ := successfulQueryPollHasSubbox hp hMax.1 hi hAction hSuccess
  exact noSecondQuerySubboxAtOpeningPoll hp hMax.1 hg hw hBlocked hCta hBox

end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
