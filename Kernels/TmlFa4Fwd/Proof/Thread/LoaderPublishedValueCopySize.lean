-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedValueLocation
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyCopyLength
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyKeyCopyLength

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val)

/-- Every copy in a recurring V publication reads a full sixteen-byte vector. -/
theorem PublishedCopyGroup.recurringValueMemberFullSize {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g index owner use : Nat}
    (group : PublishedCopyGroup l X (g,index))
    (hPub : X.AsyncArrive (g,index) (readyObject l owner (kvUseStage use)) true)
    (hPhase : (atPrefix l X g index).published.countP
      (fun q => q.slot == kvUseStage use) = use/3)
    (hUse : 2 ≤ use) (hValue : group.publication.packet.plane = .value)
    {i : Nat} {sp : AsyncCopy.Spec} (hMember : (i,sp) ∈ group.copies) :
    sp.src.size = 16 := by
  have hRank : 3*((atPrefix l X g index).published.countP
      (fun q => q.slot == kvUseStage use))+(kvUseStage use).val = use := by
    rw [hPhase,kvUseStage_val]
    omega
  have hPeriod := group.recurringOfReadyUse hp hX hPub (hRank.symm ▸ hUse)
  obtain ⟨site,hPacket,hGeom⟩ := group.recurringCoordinates hp hX hPub hPeriod
  obtain ⟨pair,upper,hCopy,_⟩ := hGeom hMember
  have hClass : site = 1 ∨ site = 3 := by
    have hPlane := (congrArg Packet.plane hPacket).trans hValue
    fin_cases site <;> first | exact .inl rfl | exact .inr rfl | cases hPlane
  rcases hClass with rfl | rfl
  · exact WarmValueSite.fullSourceSize hp hX hFrame ⟨pair,upper,hCopy⟩
  · exact SteadyValueSite.fullSourceSize hp hX hFrame ⟨pair,upper,hCopy⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
