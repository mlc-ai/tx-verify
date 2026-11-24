-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringKeyLocation
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedUse
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val recurringPacketSite)

/-- A published K member has the exact launch row of the ready ring use it supplies. -/
theorem PublishedCopyGroup.memberKeyLocation {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g index owner use : Nat}
    (group : PublishedCopyGroup l X (g,index))
    (hPub : X.AsyncArrive (g,index) (readyObject l owner (kvUseStage use)) true)
    (hPhase : (atPrefix l X g index).published.countP
      (fun q => q.slot == kvUseStage use) = use/3)
    (hUse : 2 ≤ use) (hKey : group.publication.packet.plane = .key)
    {i : Nat} {sp : AsyncCopy.Spec} (hMember : (i,sp) ∈ group.copies) :
    ∃ batch < p.batch, ∃ visit pair upper,
      RecurringKeyVectorLocation p l X (g,i) sp batch visit pair upper ∧ use = 2*visit ∧
      sp.dst = {loc := ⟨.shared,g/l.block,
        kvCopyAddress l.sharedBase (kvUseStage use) (g%l.block) pair upper⟩, size := 16} := by
  have hRank : 3*((atPrefix l X g index).published.countP
      (fun q => q.slot == kvUseStage use))+(kvUseStage use).val = use := by
    rw [hPhase,kvUseStage_val]
    omega
  have hRepeat := hRank.symm ▸ hUse
  have hPeriod := group.recurringOfReadyUse hp hX hPub hRepeat
  obtain ⟨hCursor,e,he,hMark⟩ := readyPublicationOccurrence hp hX hPub hRepeat
  have hExact := (group.memberUse hp hX he hMark hMember).trans (hCursor.trans hRank)
  obtain ⟨site,hPacket,hGeom⟩ := group.recurringCoordinates hp hX hPub hPeriod
  obtain ⟨pair,upper,hCopy,hDst⟩ := hGeom hMember
  have hClass : site = 0 ∨ site = 2 := by
    have hPlane := (congrArg Packet.plane hPacket).trans hKey
    fin_cases site <;> first | exact .inl rfl | exact .inr rfl | cases hPlane
  have hSource : ∃ batch < p.batch, ∃ visit,
      RecurringKeyVectorLocation p l X (g,i) sp batch visit pair upper := by
    rcases hClass with rfl | rfl
    · exact warmKeyVectorLocationOfUse hp hX hFrame pair upper hCopy
    · exact steadyKeyVectorLocationOfUse hp hX hFrame pair upper hCopy
  obtain ⟨batch,hb,visit,loc⟩ := hSource
  refine ⟨batch,hb,visit,pair,upper,loc,hExact.symm.trans loc.use,?_⟩
  rw [← group.slotFor hp hX hPub]
  exact hDst

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
