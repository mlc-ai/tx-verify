-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CachePublicationOutput
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A consuming ready generation at or after the selected copy's logical use
has an actual publication that tracks the copy on its own producer lane. -/
theorem CacheUseBeforeCommit.publicationOfOccurrence {copy final : EvId} {s : Spec} {loc : Loc}
    {slot : Fin 3} {phase : Nat} (hUse : CacheUseBeforeCommit l X final slot phase loc)
    (hCopy : X.Copy copy s) (hCta : copy.1 / l.block = final.1 / l.block)
    (hRank : Thread.Loader.recurringUseBefore X copy ≤ 3 * phase + slot.val) :
    ∃ publication, TraceBefore X copy publication ∧
      X.AsyncArrive publication (Thread.Loader.readyObject l final.1 slot) true ∧
      LoaderReady.generation l X publication slot = phase := by
  obtain ⟨ready, mma, _, _, _, _, _, ⟨hReady⟩, hRead, hCommit, _, _⟩ := hUse
  obtain ⟨lane, hLane⟩ := Thread.Loader.copyProducer hp hX hCopy
  obtain ⟨publication, hProducer, hArrival, _, hPhase, _⟩ :=
    hReady.actualPublicationOfLane hp hX lane
  have hOwner : ready.1 = final.1 := hRead.1.trans hCommit.1
  have hSame : publication.1 = copy.1 := by
    rw [hProducer, hOwner, ← hCta]
    exact hLane.symm
  have hPublication :
      X.AsyncArrive publication (Thread.Loader.readyObject l final.1 slot) true :=
    hOwner ▸ hArrival
  refine ⟨publication, ?_, hPublication, hPhase⟩
  apply Thread.Loader.copyBeforeReadyPublicationOfOccurrence hp hX hCopy hPublication hSame.symm
  change Thread.Loader.recurringUseBefore X copy ≤
    3 * LoaderReady.generation l X publication slot + slot.val
  rwa [hPhase]

/-- The observed ready generation suffices when it has a publication following the
copy on its actual producer lane. An arrive-on tracks that copy even if a separate
ordinary commit closes an earlier group. -/
private theorem cacheBeforeSecondStagingOfLaterObservedPublication {copy writer : EvId} {s : Spec}
    {a : Acc} {data : List Byte} {loc : Loc} (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (hStage : Thread.StageStagingWrite X writer 1 a data) (hOther : a.Covers loc)
    (hUse : ∀ final spec, Thread.SecondOutputCommit X final spec →
      SameCta l final.1 writer.1 →
        ∃ (slot : Fin 3) (phase : Nat) (publication : EvId),
          TraceBefore X copy publication ∧
          X.AsyncArrive publication (Thread.Loader.readyObject l final.1 slot) true ∧
          LoaderReady.generation l X publication slot = phase ∧
          CacheUseBeforeCommit l X final slot phase loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  apply cacheBeforeSecondStagingOfOperand hp hX hCopy hCover hStage hOther
  intro final spec hFinal hCta
  obtain ⟨slot, phase, publication, hCopyBefore, hPublication, hGeneration, hWitness⟩ :=
    hUse final spec hFinal hCta
  obtain ⟨ready, mma, d, operands, accum, mask, index, ⟨hReady⟩, hAcquire, hBefore, hMma, hLoc⟩ :=
    hWitness
  have hOwner : ready.1 = final.1 := hAcquire.1.trans hBefore.1
  obtain ⟨lane, hLane⟩ := Thread.Loader.copyProducer hp hX hCopy
  have hPublication' :
      X.AsyncArrive publication (Thread.Loader.readyObject l ready.1 slot) true :=
    hOwner.symm ▸ hPublication
  have hProducer : publication.1 = Thread.Loader.producer l (ready.1 / l.block) lane := by
    have hCtaEq : copy.1 / l.block = ready.1 / l.block :=
      (congrArg (fun g => g / l.block) hCopyBefore.1).trans
        (LoaderReady.publicationCta hp hX hPublication').symm
    rw [← hCopyBefore.1, ← hCtaEq]
    exact hLane
  obtain ⟨actual, hActual, hArrival, hPhase, hOrder⟩ :=
    hReady.publicationBeforeOperand hp hX
      (LoaderReady.actualEmptyGuardLower hp hX ready.1 slot) (isB := true) (index := index)
      lane hMma hAcquire hLoc
  have hSame := Thread.Loader.publicationUniqueAtSlot hp hX hPublication' hArrival
    (hProducer.trans hActual.symm) (hGeneration.trans hPhase.symm)
  subst actual
  have hTracked : TracksCpAsync X copy publication :=
    ⟨hCopyBefore.1, hCopyBefore.2.1, ⟨s, hCopy, (actualCopyShape hX hCopy).completion⟩,
      _, true, hPublication'⟩
  obtain ⟨_, hSource⟩ := hOrder copy s hTracked hCopy hCover
  exact ⟨mma, d, operands, accum, mask, index, hMma, hBefore, hLoc, .direct hSource⟩

/-- A recurring operand read of the byte at a sufficient logical occurrence
establishes the write order before overlapping second-stage staging. -/
theorem recurringCacheBeforeSecondStagingOfUse {copy writer : EvId} {s : Spec} {a : Acc}
    {data : List Byte} {loc : Loc} (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (hStage : Thread.StageStagingWrite X writer 1 a data) (hOther : a.Covers loc)
    (hCta : copy.1 / l.block = writer.1 / l.block)
    (hUse : ∀ final spec, Thread.SecondOutputCommit X final spec →
      copy.1 / l.block = final.1 / l.block →
        ∃ (slot : Fin 3) (phase : Nat),
          Thread.Loader.recurringUseBefore X copy ≤ 3 * phase + slot.val ∧
          CacheUseBeforeCommit l X final slot phase loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  apply cacheBeforeSecondStagingOfLaterObservedPublication hp hX hCopy hCover hStage hOther
  intro final spec hFinal hSame
  have hOwner := hCta.trans hSame.2.2.symm
  obtain ⟨slot, phase, hRank, hCache⟩ := hUse final spec hFinal hOwner
  obtain ⟨publication, hBefore, hPublish, hGeneration⟩ :=
    hCache.publicationOfOccurrence hp hX hCopy hOwner hRank
  exact ⟨slot, phase, publication, hBefore, hPublish, hGeneration, hCache⟩

/-- The same operand-use condition covers the pending second-stage output read. -/
theorem recurringCacheBeforePendingOutputOfUse {copy issue : EvId} {address x y byte : Nat}
    {s : Spec} {spec : TensorStore.Spec} {loc : Loc} (hCopy : X.Copy copy s)
    (hCover : s.dst.Covers loc) (hStore : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y byte = some loc)
    (hUse : ∀ final commit, Thread.SecondOutputCommit X final commit →
      copy.1 / l.block = final.1 / l.block →
        ∃ (slot : Fin 3) (phase : Nat),
          Thread.Loader.recurringUseBefore X copy ≤ 3 * phase + slot.val ∧
          CacheUseBeforeCommit l X final slot phase loc) :
    ByteCausality l X loc (.async copy (.write .copy))
      (.async issue (.read (.store x y byte))) := by
  apply cacheBeforePendingOutputAfterStaging hp hX hCopy hCover hStore hRead
  intro writer a data hStage hOther hProducer
  exact recurringCacheBeforeSecondStagingOfUse hp hX hCopy hCover hStage hOther hProducer hUse

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
