-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheOperandOrder
import Kernels.TmlFa4Fwd.Proof.Thread.SelectedCacheCopyUse
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInitialKeyGroup
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingDestination
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheCopyOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheExact

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvCopyVectorsApart)

private theorem equalCopyVectorsSameSlot {base a b : Nat} {sp tp : Fin 16} {u v : Bool}
    {s t : Fin 3} (hBase : base % 1024 = 0)
    (hSame : kvCopyAddress base s a sp u = kvCopyAddress base t b tp v) : s = t := by
  apply Fin.ext
  by_contra hDifferent
  have hApart := kvCopyVectorsApart (a := a) (b := b) (u := u) (v := v)
    hBase sp.isLt tp.isLt (Or.inl hDifferent)
  rcases hApart with h | h <;> omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every copy covering the B operand of a priming PV fragment is either the
selected priming V writer or ordered after the actual read. -/
theorem initialValueCopyCompetitors (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat} {op : OperandSpec} {accum : Bool}
    {mask : List Nat} (hValue : PvInstruction X (g,index) block step d op accum mask)
    (hUse : Thread.Mma.LatestValueReadyUse l X g index 1) {byte j : Nat} {pub : EvId} {loc : Loc}
    {spec : Spec} {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l g 1) true)
    (hPhase : generation l X pub 1 = 0) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hCover : spec.dst.Covers loc) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async other (.write .copy)) := by
  intro other copy hCopy hOther
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with hKey | hValueCopy | hRepeat
  · obtain ⟨pair,upper,hKey⟩ := hKey
    have hKeyDst := hKey.initialKeyDestination hp hX
    obtain ⟨otherPair,otherUpper,hDst⟩ := group.destination hp hX hPub hMember
    dsimp only at hDst
    rw [group.slotFor hp hX hPub] at hDst
    have hSelected := ((group.member j spec).mp hMember).2.2
    have hSame := (Thread.Loader.overlappingCopiesSameDestination hp hX hCopy hSelected
      hOther hCover).2
    have hEqual := congrArg (fun a : Acc => a.loc.addr) (hKeyDst.symm.trans (hSame.trans hDst))
    have hSlot := equalCopyVectorsSameSlot hp.shared.1 (s := 0) (t := 1) hEqual
    exact (by decide : (0 : Fin 3) ≠ 1) hSlot |>.elim
  · obtain ⟨pair,upper,hOtherValue⟩ := hValueCopy
    have hSelected := ((group.member j spec).mp hMember).2.2
    have hSame := (Thread.Loader.overlappingCopiesSameDestination hp hX hCopy hSelected
      hOther hCover).1
    have hOtherMember := hOtherValue.memberOfInitialPublication hp hX
      (publication := pub) hSame group hPub hPhase
    have hIndex := (coveringCopyUniqueInGeneration hp hX group group hPub hPub rfl
      hOtherMember hMember hOther hCover).2
    exact .inl (Prod.ext hSame hIndex)
  · obtain ⟨event,he,hVector,hKind⟩ := hRepeat
    have hLater : 1 < Thread.Loader.recurringUseBefore X other := by
      unfold Thread.Loader.recurringUseBefore
      omega
    exact .inr (valueReadBeforeFutureCoveringVector hp hX hValue hUse hByte
      he hVector hKind hOther hLater)

/-- Every copy covering an opening QK B read is either its selected priming
key writer or follows the actual read through a later empty acquire. -/
theorem initialKeyCopyCompetitors (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma pub : EvId} {stage : Fin 2} {d byte j : Nat} {op : OperandSpec} {accum : Bool}
    {mask : List Nat} {loc : Loc} {spec : Spec}
    (hInit : Thread.Mma.InitialQueryFragment X stage mma) (hMma : X.MmaIssue mma d op accum mask)
    {group : Thread.Loader.PublishedCopyGroup l X pub}
    (hPub : X.AsyncArrive pub (Thread.Loader.readyObject l mma.1 0) true)
    (hPhase : generation l X pub 0 = 0) (hMember : (j,spec) ∈ group.copies)
    (hByte : op.byteLoc .b byte = some loc) (hCover : spec.dst.Covers loc) :
    ∀ other copy, X.Copy other copy → copy.dst.Covers loc →
      other = (pub.1,j) ∨
      modelCausality l X loc (.async mma (.mmaRead true byte)) (.async other (.write .copy)) := by
  intro other copy hCopy hOther
  have hSelected := ((group.member j spec).mp hMember).2.2
  obtain ⟨hSame,hSameDst⟩ := Thread.Loader.overlappingCopiesSameDestination hp hX
    hCopy hSelected hOther hCover
  obtain ⟨pair,upper,hDst⟩ := group.destination hp hX hPub hMember
  dsimp only at hDst
  rw [group.slotFor hp hX hPub] at hDst
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with hKey | hValue | hRepeat
  · obtain ⟨otherPair,otherUpper,hOtherKey⟩ := hKey
    have hOtherMember := hOtherKey.memberOfInitialPublication hp hX
      (publication := pub) hSame group hPub hPhase
    have hIndex := (coveringCopyUniqueInGeneration hp hX group group hPub hPub rfl
      hOtherMember hMember hOther hCover).2
    exact .inl (Prod.ext hSame hIndex)
  · obtain ⟨otherPair,otherUpper,hValue⟩ := hValue
    have hOtherDst := hValue.initialValueDestination hp hX
    have hEqual := congrArg (fun a : Acc => a.loc.addr) (hOtherDst.symm.trans (hSameDst.trans hDst))
    have hSlot := equalCopyVectorsSameSlot hp.shared.1 (s := 1) (t := 0) hEqual
    exact (by decide : (1 : Fin 3) ≠ 0) hSlot |>.elim
  · obtain ⟨producer,index⟩ := other
    obtain ⟨event,he,hVector,hKind⟩ := hRepeat
    obtain ⟨otherPair,otherUpper,hOtherDst⟩ :=
      Thread.Loader.pendingRecurringVectorDestination hp hX he hVector hKind
    let next := Thread.Loader.recurringUseBefore X (producer,index)
    have hEqual := congrArg (fun a : Acc => a.loc.addr) (hOtherDst.symm.trans (hSameDst.trans hDst))
    have hSlot := equalCopyVectorsSameSlot hp.shared.1 (s := kvUseStage next) (t := 0) hEqual
    have hMod : next%3 = 0 := congrArg Fin.val hSlot
    have hLower : 2 ≤ next := by unfold next Thread.Loader.recurringUseBefore; omega
    have hPositive : 0 < next/3 := by omega
    obtain ⟨wait,issuer,position,release,hWait,hResume,_,hSeen⟩ :=
      pendingCacheGuardObservedReleaseExact hp hX he hVector hKind hPositive
    have hCta : mma.1/l.block = issuer/l.block := by
      rw [← release.issuerCta hp hX, hResume.1.1]
      rw [hSame]
      exact publicationCta hp hX (i := pub) hPub
    obtain hLane := Thread.Mma.sameCacheReleaseIssuer hp hX hMma release.issue hCta
    have hRelease : Thread.Mma.ReleaseIssue X mma.1 release.index release.form release.spec :=
      hLane.symm ▸ release.issue
    obtain ⟨_,hEarlier,hLength⟩ := hInit.beforeCacheRelease hX hRelease
    have hBefore : TraceBefore X mma (issuer,release.index) :=
      ⟨hLane,hEarlier,hLane ▸ hLength⟩
    exact .inr (observedOperandBeforeReuse hp hX (isB := true) release hSeen hWait
      hMma hBefore hByte hResume hCopy hOther).2

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
