-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX
open PTX.Kernels.TmlFa4Fwd.Loader (packetPlanePc vCopyPc kvUseStage_val)

/-- The physical slot-one publication of ordinal zero is the priming value packet. -/
theorem PublishedCopyGroup.initialValuePacket {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {publication : EvId} {owner : Nat} (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (readyObject l owner 1) true)
    (hFirst : (atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == 1) = 0) :
    group.publication.packet = ⟨.priming,.value⟩ := by
  obtain ⟨g,j⟩ := publication
  have hSlot := group.slotFor hp hX hPub
  have hPrim : group.publication.packet.period = .priming := by
    by_contra hRec
    obtain ⟨hS,_,hGen⟩ :=
      recurringPublicationSlotPlaneAndGeneration hp hX hPub group.published hRec
    have hValue := congrArg Fin.val (hS.symm.trans hSlot)
    rw [kvUseStage_val] at hValue
    rw [hSlot,hFirst] at hGen
    rw [group.published] at hValue hGen
    simp only [Fin.val_one,List.countP_cons,decide_eq_true hRec,↓reduceIte] at hValue hGen
    omega
  have hPlane := publicationPlaneOfGeneration hp hX hPub group.published
  dsimp only at hPlane
  rw [hSlot,hFirst] at hPlane
  cases hPacket : group.publication.packet with
  | mk period plane =>
    simp only [hPacket] at hPrim
    have hPlane' : plane = .value := by simpa [hPacket] using hPlane
    subst period plane
    rfl

/-- A member of the published priming V group is the actual vector on its destination. -/
theorem PublishedCopyGroup.primingValueMember {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} (group : PublishedCopyGroup l X issue) {target : Loc}
    (hIssue : X.AsyncArrive issue target true)
    (hPacket : group.publication.packet = ⟨.priming, .value⟩)
    {j : Nat} {spec : AsyncCopy.Spec} (hMember : (j, spec) ∈ group.copies) :
    ∃ pair : Fin 16, ∃ upper : Bool, PrimingValueVector X (issue.1, j) pair upper spec ∧
      let addr := kvCopyAddress l.sharedBase group.publication.slot (issue.1 % l.block) pair upper
      spec.dst = {loc := ⟨.shared, issue.1 / l.block, addr⟩, size := 16} := by
  have hPeriod := congrArg Packet.period hPacket
  obtain ⟨site, hSite, hGeometry⟩ := primingGroupGeometry hp hX group hIssue hPeriod
  rw [hPacket] at hSite
  have hOne : site = 1 := by fin_cases site <;> first | rfl | cases hSite
  subst site
  obtain ⟨pair, upper, hGet, hDst⟩ := hGeometry hMember
  have hPc : packetPlanePc 1 pair upper = vCopyPc pair + if upper then 1 else 0 := by
    fin_cases pair <;> cases upper <;> decide
  exact ⟨pair, upper, by simpa only [PrimingValueVector, hPc] using hGet, hDst⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
