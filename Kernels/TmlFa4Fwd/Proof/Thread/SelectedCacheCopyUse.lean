-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedUse
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInitialValueGroup
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingCopyGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX
open PTX.Kernels.TmlFa4Fwd.Loader
  (kvUseStage kvUseStage_val packetPlanePc recurringPacketSite primingPacketSite kCopyPc vCopyPc
   copyPacketFirst copyCommitPc actualPrimingCopyCheckpoint primingCopyDestinationFromEntry)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A selected member of a recurring publication is a real vector issued at the
physical packet's exact logical use. -/
theorem PublishedCopyGroup.recurringMemberAtUse {issue : EvId}
    (group : PublishedCopyGroup l X issue) {owner use : Nat}
    (hPub : X.AsyncArrive issue (readyObject l owner (kvUseStage use)) true)
    (hPhase : (atPrefix l X issue.1 issue.2).published.countP
      (fun q => q.slot == kvUseStage use) = use/3) (hRecurring : 2 ≤ use) {j : Nat}
    {spec : AsyncCopy.Spec} (hMember : (j,spec) ∈ group.copies) :
    recurringUseBefore X (issue.1,j) = use ∧
      ∃ e, X.get (issue.1,j) = some e ∧ recurringVectorEvent e ∧ e.kind = .copy spec := by
  obtain ⟨g,index⟩ := issue
  let slot := kvUseStage use
  let rank := 3 * (atPrefix l X g index).published.countP (fun q => q.slot == slot) + slot.val
  have hRank : rank = use := by
    dsimp only [rank]
    change (atPrefix l X g index).published.countP (fun q => q.slot == slot) = use/3 at hPhase
    rw [hPhase]
    change 3 * (use/3) + use%3 = use
    omega
  have hUse : 2 ≤ rank := hRank.symm ▸ hRecurring
  obtain ⟨hCursor,e,he,hMark⟩ := readyPublicationOccurrence hp hX hPub hUse
  have hPeriod := group.recurringOfReadyUse hp hX hPub hUse
  obtain ⟨site, _, hGeometry⟩ := group.recurringCoordinates hp hX hPub hPeriod
  obtain ⟨pair,upper,hGet,_⟩ := hGeometry hMember
  refine ⟨(group.memberUse hp hX he hMark hMember).trans (hCursor.trans hRank),
    _, hGet, ⟨site,pair,upper,spec,rfl⟩, rfl⟩

private theorem primingVectorDestination (stage : Fin 2) (pair : Fin 16) (upper : Bool)
    {g index : Nat} {spec : AsyncCopy.Spec}
    (he : X.get (g,index) = some ⟨packetPlanePc (primingPacketSite stage) pair upper, .copy spec⟩) :
    spec.dst = {loc := ⟨.shared,g/l.block,
      kvCopyAddress l.sharedBase stage (g%l.block) pair upper⟩, size := 16} := by
  let packet := primingPacketSite stage
  have hBound : copyPacketFirst packet ≤ packetPlanePc packet pair upper ∧
      packetPlanePc packet pair upper < copyCommitPc packet := by
    fin_cases stage <;> fin_cases pair <;> cases upper <;> decide
  obtain ⟨_,_,_,_,hAt,hWalk,hSeen⟩ :=
    actualPrimingCopyCheckpoint hp hX stage he hBound.1 hBound.2
  exact primingCopyDestinationFromEntry hp stage pair upper hAt hWalk (List.mem_of_getElem? hSeen)

/-- An issued priming K vector writes the fixed initial key slot. -/
theorem PrimingKeyVector.initialKeyDestination {copy : EvId} {pair : Fin 16} {upper : Bool}
    {spec : AsyncCopy.Spec} (hKey : PrimingKeyVector X copy pair upper spec) :
    spec.dst = {loc := ⟨.shared,copy.1/l.block,
      kvCopyAddress l.sharedBase 0 (copy.1%l.block) pair upper⟩, size := 16} := by
  obtain ⟨g,index⟩ := copy
  apply primingVectorDestination hp hX 0 pair upper (index := index)
  have hPc : packetPlanePc (primingPacketSite 0) pair upper =
      kCopyPc pair + (if upper then 1 else 0) := by fin_cases pair <;> cases upper <;> decide
  rwa [hPc]

/-- An issued priming V vector writes the fixed initial value slot. -/
theorem PrimingValueVector.initialValueDestination {copy : EvId} {pair : Fin 16} {upper : Bool}
    {spec : AsyncCopy.Spec} (hValue : PrimingValueVector X copy pair upper spec) :
    spec.dst = {loc := ⟨.shared,copy.1/l.block,
      kvCopyAddress l.sharedBase 1 (copy.1%l.block) pair upper⟩, size := 16} := by
  obtain ⟨g,index⟩ := copy
  apply primingVectorDestination hp hX 1 pair upper (index := index)
  have hPc : packetPlanePc (primingPacketSite 1) pair upper =
      vCopyPc pair + (if upper then 1 else 0) := by fin_cases pair <;> cases upper <;> decide
  rwa [hPc]

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
