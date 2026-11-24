-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedPrimingValue
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (packetPlanePc vCopyPc)

private theorem primingValuePacketPc (pair : Fin 16) (upper : Bool) :
    packetPlanePc 1 pair upper = vCopyPc pair + if upper then 1 else 0 := by
  fin_cases pair <;> cases upper <;> rfl

private theorem primingValueStationBounds (pair : Fin 16) (upper : Bool) :
    810 ≤ packetPlanePc 1 pair upper ∧ packetPlanePc 1 pair upper ≤ 902 := by
  fin_cases pair <;> cases upper <;> decide

/-- An issued priming value vector names one of the CTA's actual loader producers. -/
theorem PrimingValueVector.producerLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy : EvId} {pair : Fin 16} {upper : Bool} {s : AsyncCopy.Spec}
    (h : PrimingValueVector X copy pair upper s) :
    ∃ lane : Fin 64, copy.1 = producer l (copy.1 / l.block) lane :=
  copyProducer hp hX h.copy

/-- If the first V group from this loader has published, it contains the issued
priming vector at its actual event index. -/
theorem PrimingValueVector.memberOfInitialPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy publication : EvId} {pair : Fin 16} {upper : Bool} {s : AsyncCopy.Spec} {owner : Nat}
    (hCopy : PrimingValueVector X copy pair upper s) (hSame : copy.1 = publication.1)
    (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (readyObject l owner 1) true)
    (hFirst : (atPrefix l X publication.1 publication.2).published.countP
      (fun pub => pub.slot == 1) = 0) : (copy.2, s) ∈ group.copies := by
  have hPacket := group.initialValuePacket hp hX hPub hFirst
  obtain ⟨index, spec, hMember, hObserved⟩ :=
    group.primingValueVector hp hX hPub hPacket pair upper
  obtain ⟨g, j⟩ := copy
  have hOwn : X.get (g, j) = some ⟨packetPlanePc 1 pair upper, .copy s⟩ := by
    rwa [primingValuePacketPc]
  rw [← hSame] at hObserved
  have hIndex := uniquePrimingCopy hp hX (copyLoaderWarp hp hX hCopy.copy)
    (.inr (primingValueStationBounds pair upper)) hOwn hObserved
  subst index
  have hSpec := congrArg Event.kind (Option.some.inj (hOwn.symm.trans hObserved))
  cases hSpec
  exact hMember

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
