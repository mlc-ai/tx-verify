-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheWriteOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.PrimingCachePublicationOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyReleaseBank
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCopyCoordinates
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (PrimingCacheVector recurringUseBefore recurringVectorEvent)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvCopyVectorsApart)
open PTX.Kernels.TmlFa4Fwd.Mma (qkKCopyByteLoc qkByteIndex initialQkBlock)

/-- An issued priming cache vector is ordered before every overlapping
replacement copy by the latter's matched empty acquisition. -/
theorem primingCopyBeforeRecurringCopy {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {old next : EvId} {s t : Spec} {stage : Fin 2} {pair : Fin 16} {upper : Bool}
    (hOld : PrimingCacheVector X old stage pair upper s)
    {e : Event} (he : X.get next = some e) (hVector : recurringVectorEvent e)
    (hKind : e.kind = .copy t) {loc : Loc}
    (hCover : s.dst.Covers loc) (hOther : t.dst.Covers loc) :
    modelCausality l X loc (.async old (.write .copy)) (.async next (.write .copy)) := by
  obtain ⟨g,index⟩ := next
  let use := recurringUseBefore X (g,index)
  let slot := kvUseStage use
  let start : Fin 3 := ⟨stage.val,by have := stage.isLt; omega⟩
  have hPriming := hOld.destination hp hX
  obtain ⟨lane,vector,high,offset,hOff,hLoc⟩ :=
    Thread.Loader.pendingCopyCoveredCoordinates hp hX he hVector hKind hOther
  let first := kvCopyAddress l.sharedBase start (old.1%l.block) pair upper
  let later := kvCopyAddress l.sharedBase slot lane vector high
  have hByteAddr : loc.addr = later+offset := congrArg Loc.addr hLoc
  have hCover' := hPriming ▸ hCover
  have hLo : first ≤ loc.addr := hCover'.2.2.1
  have hHi : loc.addr < first+16 := hCover'.2.2.2
  have hSlot : slot = start := by
    apply Fin.ext
    by_contra! hNo
    have hApart := kvCopyVectorsApart
      (a := lane.val) (b := old.1%l.block) (u := high) (v := upper) hp.shared.1
      vector.isLt pair.isLt (.inl hNo)
    rcases hApart with h | h
    · change later+16 ≤ first at h
      omega
    · change first+16 ≤ later at h
      omega
  have hSmall : use % 3 < 2 := by
    change slot.val < 2
    rw [hSlot]
    exact stage.isLt
  have hLower : 2 ≤ use := by unfold use recurringUseBefore; omega
  have hPositive : 0 < use/3 := by omega
  obtain ⟨wait,issuer,position,release,hEmpty,hGuard,_,hObserved⟩ :=
    pendingCacheGuardObservedReleaseExact hp hX he hVector hKind hPositive
  have hOwner : g/l.block = issuer/l.block :=
    (congrArg (· / l.block) hGuard.1.1.symm).trans (release.issuerCta hp hX)
  have hLoc' : loc = ⟨.shared,issuer/l.block,later+offset⟩ := by
    simpa only [Prod.fst,hOwner] using hLoc
  have hCopy := Thread.Loader.actualCopyOfRecurringVector he hVector hKind
  obtain ⟨i,d,byte,op,accum,mask,hIssue,hAfter,hBefore,hRead⟩ :
      ∃ i d byte op accum mask, X.MmaIssue (issuer,i) d op accum mask ∧
        TraceBefore X (issuer,release.matched.wait) (issuer,i) ∧
        TraceBefore X (issuer,i) (issuer,release.index) ∧ op.byteLoc .b byte = some loc := by
    rw [hLoc']
    have hForms (form : Thread.Mma.ReleaseForm) :
        form = .firstKey ∨ form = .loopKey ∨ form = .loopValue ∨ form = .tailValue := by
      cases form <;> decide
    rcases hForms release.form with hForm | hForm | hForm | hForm
    · have hInitial := release.firstKeyUse hp hX hForm
      change 3 * release.ordinal + slot.val = 0 at hInitial
      have hZero : slot.val = 0 := by omega
      obtain ⟨fragment,row,k,byte,hRow,hK,hByte,hCoordinate⟩ :=
        Output.initialKeyByteOfVector l (issuer/l.block) lane vector high hOff
      obtain ⟨i,d,op,accum,mask,hKey,hAfter,hBefore,hAddress⟩ :=
        release.firstKeyBank hp hX hForm 0 fragment
      have hByteLoc := hAddress (qkByteIndex row k byte)
      rw [qkKCopyByteLoc l issuer (initialQkBlock 0) fragment 0 hp.shared.1
        hRow hK hByte] at hByteLoc
      change op.byteLoc .b (qkByteIndex row k byte) =
        some (Thread.initialKeyByte l (issuer/l.block) fragment row k byte) at hByteLoc
      rw [hCoordinate] at hByteLoc
      refine ⟨i,d,qkByteIndex row k byte,op,accum,mask,⟨_,hKey.decoded⟩,hAfter,hBefore,?_⟩
      simpa only [later,hZero] using hByteLoc
    · obtain ⟨_,i,d,byte,op,accum,mask,hKey,hAfter,hBefore,hRead⟩ :=
        Output.recurringKeyVectorReadOfRelease hp hX release hForm 0 lane vector high hOff
      exact ⟨i,d,byte,op,accum,mask,⟨_,hKey.decoded⟩,hAfter,hBefore,hRead⟩
    · exact valueVectorReadOfRelease hp hX release true hForm 0 lane vector high hOff
    · exact valueVectorReadOfRelease hp hX release false hForm 0 lane vector high hOff
  apply copyBeforeGuardedCopyThroughPublication hp hX release hObserved hEmpty hGuard hCopy
    hOther hOld.copy hCover _ hIssue hAfter hBefore hRead
  intro publication hLane hPub _
  change X.AsyncArrive publication (Thread.Loader.readyObject l issuer slot) true at hPub
  rw [hSlot] at hPub
  exact hOld.beforeSameSlotPublication hp hX hLane hPub

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
