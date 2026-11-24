-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (packetPlanePc kCopyPc kvUseStage_val)

private theorem primingKeyPc (pair : Fin 16) (upper : Bool) :
    packetPlanePc 0 pair upper = kCopyPc pair + if upper then 1 else 0 := by
  fin_cases pair <;> cases upper <;> rfl

private theorem keySiteBounds (pair : Fin 16) (upper : Bool) :
    550 ≤ packetPlanePc 0 pair upper ∧ packetPlanePc 0 pair upper ≤ 672 := by
  fin_cases pair <;> cases upper <;> decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem primingKeyWarp {g j : Nat} {pair : Fin 16} {upper : Bool} {s : AsyncCopy.Spec}
    (h : PrimingKeyVector X (g,j) pair upper s) :
    14 ≤ warpIndex l g := by
  have hc : X.get (g,j) = some ⟨packetPlanePc 0 pair upper,.copy s⟩ := by
    rwa [primingKeyPc]
  have hb := keySiteBounds pair upper
  have hRole := roleBodyPcOfEvent hp hX hc
    (show 173 < packetPlanePc 0 pair upper by omega)
    (show packetPlanePc 0 pair upper ∉ registerHintSites by
      simp only [registerHintSites,List.mem_cons,List.not_mem_nil,or_false]
      omega)
  change roleBodyPc (warpIndex l g) (packetPlanePc 0 pair upper) at hRole
  unfold roleBodyPc at hRole
  rcases hRole with hEq | hBody
  · omega
  · split_ifs at hBody <;> omega

/-- An issued priming key vector belongs to one of the actual 64 cache producers. -/
theorem PrimingKeyVector.producerLane {copy : EvId} {pair : Fin 16} {upper : Bool}
    {s : AsyncCopy.Spec} (h : PrimingKeyVector X copy pair upper s) :
    ∃ lane : Fin 64, copy.1 = producer l (copy.1/l.block) lane := by
  obtain ⟨g,j⟩ := copy
  have hWarp := primingKeyWarp hp hX h
  have hLane : 448 ≤ g % l.block := by
    unfold warpIndex at hWarp
    omega
  have hLocal : g % l.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  let lane : Fin 64 := ⟨g % l.block - 448,by omega⟩
  refine ⟨lane,?_⟩
  change g = producer l (g/l.block) lane
  change g = g/l.block*l.block + 448 + (g % l.block - 448)
  rw [Nat.mul_comm _ l.block]
  have hDiv := Nat.mod_add_div g l.block
  omega

/-- The physical slot-zero publication of ordinal zero is the priming key packet. -/
theorem PublishedCopyGroup.initialKeyPacket {publication : EvId} {owner : Nat}
    (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (readyObject l owner 0) true)
    (hFirst : (atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == 0) = 0) :
    group.publication.packet = ⟨.priming,.key⟩ := by
  obtain ⟨g,j⟩ := publication
  have hSlot := group.slotFor hp hX hPub
  have hPrim : group.publication.packet.period = .priming := by
    by_contra hRec
    obtain ⟨hS,_,hGen⟩ :=
      recurringPublicationSlotPlaneAndGeneration hp hX hPub group.published hRec
    have hValue := congrArg Fin.val (hS.symm.trans hSlot)
    rw [kvUseStage_val] at hValue
    rw [hSlot,hFirst] at hGen
    simp only [Fin.val_zero] at hValue
    omega
  have hPlane := publicationPlaneOfGeneration hp hX hPub group.published
  dsimp only at hPlane
  rw [hSlot,hFirst] at hPlane
  cases hPacket : group.publication.packet with
  | mk period plane =>
    simp only [hPacket] at hPrim
    have hPlane' : plane = .key := by simpa [hPacket] using hPlane
    subst period plane
    rfl

/-- A previously issued priming K vector is a member of its lane's ordinal-zero
publication whenever the latter is forced by a real consumer. -/
theorem PrimingKeyVector.memberOfInitialPublication {copy publication : EvId} {pair : Fin 16}
    {upper : Bool} {s : AsyncCopy.Spec} {owner : Nat} (hCopy : PrimingKeyVector X copy pair upper s)
    (hSame : copy.1 = publication.1) (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (readyObject l owner 0) true)
    (hFirst : (atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == 0) = 0) : (copy.2,s) ∈ group.copies := by
  have hPacket := group.initialKeyPacket hp hX hPub hFirst
  obtain ⟨other,spec,hMember,hGet⟩ := group.primingKeyVector hp hX hPub hPacket pair upper
  obtain ⟨g,j⟩ := copy
  have hOwn : X.get (g,j) = some ⟨packetPlanePc 0 pair upper,.copy s⟩ := by
    rwa [primingKeyPc]
  have hWarp := primingKeyWarp hp hX hCopy
  rw [← hSame] at hGet
  have hOther := uniquePrimingCopy hp hX hWarp (.inl (keySiteBounds pair upper)) hOwn hGet
  subst other
  have he := congrArg Event.kind (Option.some.inj (hOwn.symm.trans hGet))
  cases he
  exact hMember

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
