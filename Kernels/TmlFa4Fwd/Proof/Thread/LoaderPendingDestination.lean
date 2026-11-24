-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader
  (actualRecurringCopySlotGuardLatest packetPlanePc recurringPacketSite
   recurringEmptyWait emptySlot_address kvUseStage)

/-- The exact destination of a recurring vector is fixed by its logical use
even before the producer commits or publishes the packet. -/
theorem pendingRecurringVectorDestination {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hVector : recurringVectorEvent e) {spec : AsyncCopy.Spec} (hKind : e.kind = .copy spec) :
    ∃ (pair : Fin 16) (upper : Bool),
      let slot := kvUseStage (recurringUseBefore X (g,index))
      spec.dst = {loc := ⟨.shared, g/l.block,
        kvCopyAddress l.sharedBase slot (g%l.block) pair upper⟩, size := 16} := by
  have hShape := hVector
  obtain ⟨site,pair,upper,copy,rfl⟩ := hShape
  obtain rfl := Kind.copy.inj hKind
  obtain ⟨physical, before, parity, hDst, hPhysical, hResume, hPhysicalLast⟩ :=
    actualRecurringCopySlotGuardLatest hp hX site pair upper he
  obtain ⟨start, prior, wait, _, _, hEmpty, hOrder, _, hUse,
    current, retries, hWaitId, _, ⟨observed,hObserved,hRecurring⟩, hLast⟩ :=
    actualVectorUseWithLatestGuard hp hX he hVector
  let ePhysical : Event := ⟨(recurringEmptyWait site).pc, .wait (emptyObject l g physical)
    parity true true .cta⟩
  have hPhysicalGet : X.get (g,before) = some ePhysical := hPhysical
  have hPhysicalMark : recurringEmptyEvent ePhysical := ⟨site,_,_,rfl⟩
  have hEqual : before = wait.2 := by
    rcases lt_trichotomy before wait.2 with hLt | hEq | hLt
    · have hThread : wait = (g,wait.2) := by rw [hWaitId]
      exact (hPhysicalLast wait.2 hLt hOrder.1.2.1 observed (hThread ▸ hObserved)
        hRecurring).elim
    · exact hEq
    · exact (hLast before hLt hResume.1.2.1 ePhysical hPhysicalGet hPhysicalMark).elim
  have hWait : wait = (g,before) := by
    have hThread : wait.1 = g := congrArg Prod.fst hWaitId
    exact Prod.ext hThread hEqual.symm
  have hLogical := hEmpty
  rw [hWait] at hLogical
  obtain ⟨logical, hLogicalGet, hLogicalKind⟩ := hLogical
  have hEvent : ePhysical = logical := Option.some.inj
    (hPhysicalGet.symm.trans hLogicalGet)
  have hKindEq := congrArg Event.kind hEvent
  rw [hLogicalKind] at hKindEq
  have hLoc := (Kind.wait.inj hKindEq).1
  have hPhysEq : physical = kvUseStage (recurringUseBefore X (g,index)) := by
    rw [← hUse]
    have hAddr := congrArg Loc.addr hLoc
    change (emptyObject l g physical).addr =
      (emptyObject l g (kvUseStage (2 + prior.countP recurringPublicationMark))).addr at hAddr
    exact Fin.ext (by simp only [emptyObject, emptySlot_address] at hAddr; omega)
  exact ⟨pair,upper,hPhysEq ▸ hDst⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
