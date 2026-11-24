-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
public import Kernels.TmlFa4Fwd.Proof.MmaOperandOrder
import Lemmas.Order.OrderBaseCausality
import Lemmas.Tcgen05.MmaObservedReads

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (EmptyAcquire readyObject)
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)

/-- The selected loader lane's publication of the observed generation orders every
tracked copy of the operand byte before the consuming MMA. -/
theorem Completed.publicationBeforeOperand {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait mma : EvId} {slot : Fin 3} {phase d index : Nat} {isB accum : Bool}
    {mask : List Nat} {op : TcMma.OperandSpec} {loc : Loc}
    (h : Completed l X wait slot phase) (hGuard : EmptyGuardLower l X wait.1 slot)
    (lane : Fin 64) (hMma : X.MmaIssue mma d op accum mask)
    (hEarlier : TraceBefore X wait mma)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc) :
    ∃ issue, issue.1 = Thread.Loader.producer l (wait.1 / l.block) lane ∧
      X.AsyncArrive issue (readyObject l wait.1 slot) true ∧ generation l X issue slot = phase ∧
      ∀ copy spec, TracksCpAsync X copy issue → X.Copy copy spec → spec.dst.Covers loc →
        (∃ bytes, X.MemWrites (.async copy (.write .copy)) spec.dst bytes) ∧
        modelCausality l X loc (.async copy (.write .copy)) (.async mma (.mmaRead isB index)) := by
  obtain ⟨issue, hLane, hPub, hArrived, hOrdinal, hDone⟩ :=
    h.visiblePublicationOfLane hp hX hGuard lane
  have hMmaOrigin := hMma
  obtain ⟨_, hMmaEvent⟩ := hMmaOrigin
  have hOrder : baseCausality l X wait mma :=
    .single (.inl (po_of_not_access hEarlier.1 hEarlier.2.1 hEarlier.2.2
      (by rw [hMmaEvent]; rfl)))
  refine ⟨issue, hLane, hPub, hOrdinal, ?_⟩
  intro copy spec hTrack hCopy hCover
  have hCopyOrigin := hCopy
  obtain ⟨_, hEvent⟩ := hCopyOrigin
  have hCTA : SameCta l copy.1 mma.1 := by
    refine ⟨Step.CtaBar.thread_lt_of_get hX hEvent, Step.CtaBar.thread_lt_of_get hX hMmaEvent, ?_⟩
    rw [hTrack.1, ← hEarlier.1]
    exact (publicationCta hp hX hPub).symm
  have hWhole := (actualCopyShape hX hCopy).whole
  obtain ⟨bytes, hWritten⟩ :=
    Option.isSome_iff_exists.mp ((hX.tma.2.2.2 issue hArrived).2 copy hTrack)
  exact ⟨⟨bytes, spec, hCopy, hWhole, rfl, hWritten⟩,
    Mma.packetBeforeOperand hCTA hCopy hWhole hCover hMma hLoc (hDone copy hTrack) hOrder⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait copy mma : EvId} {slot : Fin 3}
    {g k parity d index : Nat} {isB accum : Bool} {mask : List Nat} {op : TcMma.OperandSpec}
    {loc : Loc} {spec : Spec} (a : EmptyReleaseAt l X (emptyObject l wait.1 slot) g k)
    (hSeen : MbarObserved X a.record.id (.thread wait)) (hWait : EmptyAcquire l X wait slot parity)
    (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X mma (g, a.index))
    (hOperand : op.byteLoc (if isB then .b else .a) index = some loc)
    (hGuard : Resumes kernel X wait copy)
include hp hX a hSeen hWait hMma hEarlier hOperand hGuard

/-- A loader copy after the successful empty wait follows the shared operand reads tracked
by the actual release notification that the wait observed. -/
theorem observedOperandBeforeReuse (hCopy : X.Copy copy spec) (hCover : spec.dst.Covers loc) :
    X.AsyncPresent mma (.mmaRead isB index) ∧
      modelCausality l X loc (.async mma (.mmaRead isB index)) (.async copy (.write .copy)) := by
  obtain ⟨e, he, hKind⟩ := hWait
  obtain ⟨present, w, target, acquire, scope, hw, hO, _⟩ := hSeen
  have hWaitEq := Ref.thread.inj hw.symm
  subst w
  obtain ⟨⟨_, _, hw⟩, hBefore⟩ := hO
  have hEq := Kind.wait.inj ((congrArg Event.kind (Option.some.inj (hw.symm.trans he))).trans hKind)
  obtain ⟨rfl, _, _, rfl, rfl⟩ := hEq
  have hCommit : X.Commit (g, a.index) a.spec := ⟨_, a.issue⟩
  have hTrack : TracksMma X mma (g, a.index) :=
    ⟨hEarlier.1, hEarlier.2.1, .inl ⟨_, _, _, _, hMma⟩, _, hCommit⟩
  rw [a.notification] at present
  have hMmaObs : AsyncObserved X mma .mmaDone wait true .cta :=
    ⟨a.record.id, emptyObject l wait.1 slot,
      ⟨(g, a.index), a.spec, a.rank, a.notification, hTrack, hCommit, a.target, present⟩,
      ⟨⟨_, _, hw⟩, hBefore⟩⟩
  have hMmaOrigin := hMma
  have hCopyOrigin := hCopy
  obtain ⟨_, hMmaEvent⟩ := hMmaOrigin
  obtain ⟨_, hCopyEvent⟩ := hCopyOrigin
  have hm := Step.CtaBar.thread_lt_of_get hX hMmaEvent
  have hwThread := Step.CtaBar.thread_lt_of_get hX hw
  have hc := Step.CtaBar.thread_lt_of_get hX hCopyEvent
  have hCta : wait.1 / l.block = mma.1 / l.block :=
    (a.issuerCta hp hX).trans (congrArg (fun t => t / l.block) hEarlier.1).symm
  have hCopyCta : mma.1 / l.block = copy.1 / l.block :=
    hCta.symm.trans (congrArg (fun t => t / l.block) hGuard.1.1)
  have hScope : ScopesMeet l .cluster mma.1 .cta wait.1 :=
    ⟨⟨hm, hwThread, congrArg l.clusterOfCta hCta.symm⟩, ⟨hwThread, hm, hCta⟩⟩
  have hOrder : baseCausality l X wait copy :=
    .single (.inl (po_of_not_access hGuard.1.1 hGuard.1.2.1 hGuard.1.2.2
      (by rw [hCopyEvent]; rfl)))
  exact ⟨observed_mmaRead hX hMma hOperand hMmaObs,
    Mma.operandBeforePacketReuse ⟨hm, hc, hCopyCta⟩ hMma hOperand hCopy
      (actualCopyShape hX hCopy).whole hCover hMmaObs hScope hOrder⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
