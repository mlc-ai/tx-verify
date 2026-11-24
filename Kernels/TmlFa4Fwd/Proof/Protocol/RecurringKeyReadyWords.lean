-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandFinite
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReuseOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheRelease
import Kernels.TmlFa4Fwd.Proof.Thread.MmaLatestReady
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index : Nat} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
include hp hX stage hKey

/-- An actual recurring QK fragment observes a completed cache packet, and its B
operand's shared bytes are exactly those of that packet's physical key slot. -/
theorem recurringKeyFragmentReadyBytesExact :
    ∃ wait use,
      Nonempty (Completed l X (g,wait) (kvUseStage use) (use/3)) ∧
      TraceBefore X (g,wait) (g,index) ∧
      use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1 ∧
      ∀ j, op.byteLoc .b j =
        (cacheOperand l g (recurringKeyBlock stage) step use .key).byteLoc .b j := by
  obtain ⟨wait,use,hDesc,hPoll,hEarlier,hCount,hUse⟩ :=
    hKey.recurringKeyReadyUseExact hp hX stage
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  have hWarp := (mmaIssueElection hp hX hMma).1
  have hg := event_thread_lt hX hKey.decoded
  have hgWarp : Prologue.warpIndex l g = 12 := hWarp
  have hTotal := Thread.Mma.readyUsesAtPrefix hp hX hg hgWarp wait
  have hOrdinal := (hTotal.symm.trans hCount)
  have hPhase := (Thread.Mma.ReadyPoll.exactOccurrence hp hX hgWarp hPoll).2.1
  dsimp only at hOrdinal hPhase
  rw [hOrdinal] at hPhase
  change (Thread.Mma.atPrefix l X g wait).kvAcquires (readyStage use) = use/3 at hPhase
  have hDone := completedForObservedIssuer hp hX hgWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hMma) hPoll
    (actualEmptyGuardLower hp hX g (kvUseStage use))
  rw [hPhase] at hDone
  have hQ := hKey.queryOperand hp hX
  refine ⟨wait,use,hDone,hEarlier,hUse,fun j => ?_⟩
  simp only [OperandSpec.byteLoc,cacheOperand,qkOperands,hQ.descriptor,hQ.ctaLow,hQ.ctaHigh,
    hDesc,reduceCtorEq,false_and,↓reduceIte]
  rfl

/-- A recurring QK fragment reads its selected K generation at an even logical use. -/
theorem recurringKeyFragmentReadyBytesOfEvenUse :
    ∃ wait use,
      Nonempty (Completed l X (g,wait) (kvUseStage use) (use/3)) ∧
      TraceBefore X (g,wait) (g,index) ∧
      use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
        (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1 ∧
      use % 2 = 0 ∧
      ∀ j, op.byteLoc .b j =
        (cacheOperand l g (recurringKeyBlock stage) step use .key).byteLoc .b j := by
  obtain ⟨wait,use,hDone,hEarlier,hUse,hLoc⟩ :=
    recurringKeyFragmentReadyBytesExact hp hX stage hKey
  have hEven := (hKey.recurringKeyOperandOfEvenReadyUse hp hX stage).2
  exact ⟨wait,use,hDone,hEarlier,hUse,hUse.symm ▸ hEven,hLoc⟩

/-- A recurring QK read precedes an overlapping later-generation copy on the
same slot, even if the loader's packet is still open. -/
theorem recurringKeyBeforePendingCopy {producer copyIndex : Nat} {event : Event}
    (hEvent : X.get (producer,copyIndex) = some event)
    (hRecurring : Thread.Loader.recurringVectorEvent event) {byte use : Nat} {loc : Loc}
    {copy : Spec} (hKind : event.kind = .copy copy)
    (hUse : use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1) (hOperand : op.byteLoc .b byte = some loc)
    (hCover : copy.dst.Covers loc)
    (hSlot : kvUseStage (Thread.Loader.recurringUseBefore X (producer,copyIndex)) = kvUseStage use)
    (hLater : use < Thread.Loader.recurringUseBefore X (producer,copyIndex)) :
    X.AsyncPresent (g,index) (.mmaRead true byte) ∧
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async (producer,copyIndex) (.write .copy)) := by
  let next := Thread.Loader.recurringUseBefore X (producer,copyIndex)
  have hMod : next % 3 = use % 3 := congrArg Fin.val hSlot
  change use < next at hLater
  have hPositive : 0 < next/3 := by omega
  obtain ⟨wait,issuer,position,release,hWait,hResume,hLower,hSeen⟩ :=
    pendingCacheGuardObservedRelease hp hX hEvent hRecurring hPositive
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  have hCopy := Thread.Loader.actualCopyOfRecurringVector hEvent hRecurring hKind
  obtain ⟨_,_,_,_,hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  have hCopyCta : loc.cta = producer/l.block := by
    have hCovered := hDst ▸ hCover
    exact hCovered.2.1
  have hMmaCta := (hKey.keyByteRange hp hX hOperand).cta
  have hOwner : g/l.block = issuer/l.block := by
    rw [← release.issuerCta hp hX, hResume.1.1, ← hCopyCta, hMmaCta]
  obtain rfl := Thread.Mma.sameCacheReleaseIssuer hp hX hMma release.issue hOwner
  have hUseBound : use ≤ 3 * release.ordinal + (kvUseStage next).val := by
    change next/3-1 ≤ release.ordinal at hLower
    change use ≤ 3 * release.ordinal + next % 3
    omega
  have hEarlier := Thread.Mma.recurringKeyBeforeRelease hp hX stage hKey release
    (hUse ▸ hUseBound)
  exact observedOperandBeforeReuse hp hX release hSeen hWait hMma hEarlier
    hOperand hResume hCopy hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
