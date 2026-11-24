-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderMmaHandoff
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma
open Thread.Mma (EmptyReleaseAt)
open Thread.Mma.Observation (emptyObject)
open Thread.Loader (EmptyAcquire recurringUseBefore)

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {old wait copy : EvId} {oldSpec newSpec : Spec}
    {loc : Loc} {slot : Fin 3} {issuer position parity : Nat}
    (release : EmptyReleaseAt l X (emptyObject l wait.1 slot) issuer position)
    (hSeen : MbarObserved X release.record.id (.thread wait))
    (hWait : EmptyAcquire l X wait slot parity) (hGuard : Resumes kernel X wait copy)
    (hCopy : X.Copy copy newSpec) (hNew : newSpec.dst.Covers loc) (hOld : X.Copy old oldSpec)
include hp hX release hSeen hWait hGuard hCopy hNew hOld

/-- A released cache read orders any older tracked copy before the new copy that
reuses the byte whenever the observed publication tracked the old issue. -/
theorem copyBeforeGuardedCopyThroughPublication (hCover : oldSpec.dst.Covers loc)
    (hTracks : ∀ publication, old.1 = publication.1 →
      X.AsyncArrive publication (Thread.Loader.readyObject l issuer slot) true →
      generation l X publication slot = release.ordinal → TraceBefore X old publication)
    {mma : EvId} {d byte : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : X.MmaIssue mma d op accum mask)
    (hEarlier : TraceBefore X (issuer,release.matched.wait) mma)
    (hBefore : TraceBefore X mma (issuer,release.index)) (hByte : op.byteLoc .b byte = some loc) :
    modelCausality l X loc (.async old (.write .copy)) (.async copy (.write .copy)) := by
  have hReady := release.matched.ready
  rw [release.matchedSlot] at hReady
  obtain ⟨completion⟩ := actualCompletedForIssuer hp hX release.issue hReady
  have hOrdinal :
      (Thread.Mma.atPrefix l X issuer release.matched.wait).kvAcquires slot = release.ordinal :=
    congrArg ((Thread.Mma.atPrefix l X issuer release.matched.wait).kvAcquires)
      release.matchedSlot.symm
  rw [hOrdinal] at completion
  obtain ⟨hSame,_⟩ := Thread.Loader.overlappingCopiesSameDestination hp hX hOld hCopy
    hCover hNew
  have hOwner : old.1 / l.block = issuer / l.block := by
    rw [hSame,← hGuard.1.1,release.issuerCta hp hX]
  obtain ⟨lane,hLane⟩ := Thread.Loader.copyProducer hp hX hOld
  obtain ⟨publication,hProducer,hPub,hGeneration,hCopies⟩ :=
    completion.publicationBeforeOperand hp hX (actualEmptyGuardLower hp hX issuer slot) lane
      hIssue hEarlier (isB := true) hByte
  have hThread : old.1 = publication.1 := by rw [hProducer,← hOwner]; exact hLane
  have hOldBefore := hTracks publication hThread hPub hGeneration
  have hTrack : TracksCpAsync X old publication :=
    ⟨hThread,hOldBefore.2.1,⟨oldSpec,hOld,(actualCopyShape hX hOld).completion⟩,_,_,hPub⟩
  have hOldOrder := (hCopies old oldSpec hTrack hOld hCover).2
  obtain ⟨hRead,hNewOrder⟩ :=
    observedOperandBeforeReuse hp hX (isB := true) release hSeen hWait hIssue hBefore hByte
      hGuard hCopy hNew
  have hCta : SameCta l old.1 copy.1 :=
    ⟨(Thread.Loader.copyDestination hp hX hOld).1,
      (Thread.Loader.copyDestination hp hX hCopy).1,congrArg (· / l.block) hSame⟩
  exact modelCausality_async_trans hOldOrder hRead hNewOrder (.inl hCta)

/-- A released cache read orders any older tracked copy before the new copy that
reuses the byte. The old copy may belong to an earlier packet than the one consumed. -/
theorem earlierRecurringCopyBeforeGuardedCopy (hCover : oldSpec.dst.Covers loc)
    (hRank : recurringUseBefore X old ≤ 3 * release.ordinal + slot.val) {mma : EvId} {d byte : Nat}
    {op : OperandSpec} {accum : Bool} {mask : List Nat} (hIssue : X.MmaIssue mma d op accum mask)
    (hEarlier : TraceBefore X (issuer,release.matched.wait) mma)
    (hBefore : TraceBefore X mma (issuer,release.index)) (hByte : op.byteLoc .b byte = some loc) :
    modelCausality l X loc (.async old (.write .copy)) (.async copy (.write .copy)) := by
  apply copyBeforeGuardedCopyThroughPublication hp hX release hSeen hWait hGuard hCopy hNew
    hOld hCover _ hIssue hEarlier hBefore hByte
  intro publication hLane hPub hGeneration
  apply Thread.Loader.copyBeforeReadyPublicationOfOccurrence hp hX hOld hPub hLane
  change recurringUseBefore X old ≤ 3 * generation l X publication slot + slot.val
  rwa [hGeneration]
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- A real recurring key release consumes each vector byte and thereby orders
older recurring writes before a copy guarded by that release. -/
theorem earlierRecurringCopyBeforeKeyGuardedCopy (hX : Consistent l kernel Assumptions.all m X)
    {old wait copy : EvId} {oldSpec newSpec : Spec} {slot : Fin 3} {issuer position parity : Nat}
    (release : EmptyReleaseAt l X (emptyObject l wait.1 slot) issuer position)
    (hKind : release.form = .loopKey) (hSeen : MbarObserved X release.record.id (.thread wait))
    (hWait : EmptyAcquire l X wait slot parity) (hGuard : Resumes kernel X wait copy)
    (hCopy : X.Copy copy newSpec) (hOld : X.Copy old oldSpec)
    (hRank : recurringUseBefore X old ≤ 3 * release.ordinal + slot.val) (stage : Fin 2)
    (lane : Fin 64) (pair : Fin 16) (upper : Bool) {off : Nat} (hOff : off < 16)
    (hCover : oldSpec.dst.Covers
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩)
    (hNew : newSpec.dst.Covers
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩) :
    modelCausality l X
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩
      (.async old (.write .copy)) (.async copy (.write .copy)) := by
  obtain ⟨step,i,d,byte,op,accum,mask,hKey,hEarlier,hBefore,hByte⟩ :=
    Protocol.Output.recurringKeyVectorReadOfRelease hp hX release hKind stage lane pair upper hOff
  exact earlierRecurringCopyBeforeGuardedCopy hp hX release hSeen hWait hGuard hCopy hNew
    hOld hCover hRank ⟨_,hKey.decoded⟩ hEarlier hBefore hByte

/-- A delivered value release follows an actual fragment reading the chosen
byte from its matched physical cache slot. -/
theorem valueVectorReadOfRelease (hX : Consistent l kernel Assumptions.all m X)
    {owner issuer position : Nat} {slot : Fin 3}
    (release : EmptyReleaseAt l X (emptyObject l owner slot) issuer position) (steady : Bool)
    (hKind : release.form = Thread.Mma.valueReleaseForm steady) (stage : Fin 2) (lane : Fin 64)
    (pair : Fin 16) (upper : Bool) {off : Nat} (hOff : off < 16) :
    ∃ index d byte op accum mask,
      X.MmaIssue (issuer,index) d op accum mask ∧
      TraceBefore X (issuer,release.matched.wait) (issuer,index) ∧
      TraceBefore X (issuer,index) (issuer,release.index) ∧
      op.byteLoc .b byte =
        some ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩ := by
  let block := Thread.firstPvBlock steady stage
  obtain ⟨step,byte,hCoord⟩ := Protocol.Output.valueVectorHasOperandCoordinate l issuer
    block slot lane pair upper hp.shared.1 hOff
  obtain ⟨index,d,op,accum,mask,hPv,hAfter,hBefore⟩ :=
    release.valueBank hp hX steady hKind stage step
  have hStage : decide (block.val < 2) = steady := by
    dsimp only [block]
    cases steady <;> fin_cases stage <;> rfl
  have hB := Thread.Mma.valueFragmentReleasedDescriptor hp hX hPv release
    (hStage.symm ▸ hKind) hAfter hBefore
  obtain ⟨_,_,hDescriptor,hLow,hHigh⟩ := hPv.valueOperand hp hX
  have hByte : op.byteLoc .b byte =
      (Mma.pvOperands l issuer block step slot.val).byteLoc .b byte := by
    simp only [TcMma.OperandSpec.byteLoc,Mma.pvOperands,hB,hDescriptor,hLow,hHigh,
      reduceCtorEq,false_and,↓reduceIte]
    rfl
  exact ⟨index,d,byte,op,accum,mask,⟨_,hPv.decoded⟩,hAfter,hBefore,hByte.trans hCoord⟩

/-- A real steady or tail value release likewise orders older tracked writes
before a copy that reuses the covered byte. -/
theorem earlierRecurringCopyBeforeValueGuardedCopy (hX : Consistent l kernel Assumptions.all m X)
    {old wait copy : EvId} {oldSpec newSpec : Spec} {slot : Fin 3} {issuer position parity : Nat}
    (release : EmptyReleaseAt l X (emptyObject l wait.1 slot) issuer position) (steady : Bool)
    (hKind : release.form = Thread.Mma.valueReleaseForm steady)
    (hSeen : MbarObserved X release.record.id (.thread wait))
    (hWait : EmptyAcquire l X wait slot parity) (hGuard : Resumes kernel X wait copy)
    (hCopy : X.Copy copy newSpec) (hOld : X.Copy old oldSpec)
    (hRank : recurringUseBefore X old ≤ 3 * release.ordinal + slot.val) (stage : Fin 2)
    (lane : Fin 64) (pair : Fin 16) (upper : Bool) {off : Nat} (hOff : off < 16)
    (hCover : oldSpec.dst.Covers
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩)
    (hNew : newSpec.dst.Covers
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩) :
    modelCausality l X
      ⟨.shared,issuer/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩
      (.async old (.write .copy)) (.async copy (.write .copy)) := by
  obtain ⟨index,d,byte,op,accum,mask,hIssue,hAfter,hBefore,hByte⟩ :=
    valueVectorReadOfRelease hp hX release steady hKind stage lane pair upper hOff
  exact earlierRecurringCopyBeforeGuardedCopy hp hX release hSeen hWait hGuard hCopy hNew
    hOld hCover hRank hIssue hAfter hBefore hByte

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
