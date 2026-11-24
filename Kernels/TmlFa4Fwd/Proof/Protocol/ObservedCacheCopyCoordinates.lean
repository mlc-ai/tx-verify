-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingEarlier
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

namespace LoaderReady

/-- The exact completed generation supplies the coordinates of any earlier
copy at the same logical use, including the byte covered by the copy. -/
theorem Completed.recurringCopyCoveredCoordinates {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy wait : EvId} {use : Nat} (done : Completed l X wait (kvUseStage use) (use/3))
    {event : Event} (he : X.get copy = some event)
    (hVector : Thread.Loader.recurringVectorEvent event)
    {spec : Spec} (hKind : event.kind = .copy spec)
    (hUse : Thread.Loader.recurringUseBefore X copy = use)
    (hCta : copy.1 / l.block = wait.1 / l.block)
    {loc : Loc} (hCovers : spec.dst.Covers loc) :
    ∃ (lane : Fin 64) (pair : Fin 16) (upper : Bool) (offset : Nat), offset < 16 ∧
      loc = ⟨.shared, wait.1 / l.block,
        kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper + offset⟩ := by
  let slot := kvUseStage use
  have hCopy := Thread.Loader.actualCopyOfRecurringVector he hVector hKind
  obtain ⟨lane, hLane⟩ := Thread.Loader.copyProducer hp hX hCopy
  obtain ⟨publication, hPubLane, hPub, _, hPhase, _⟩ := done.actualPublicationOfLane hp hX lane
  have hOwner : publication.1 = copy.1 := by rw [hPubLane, ← hCta, ← hLane]
  obtain ⟨source,index⟩ := copy
  obtain ⟨producer,arrival⟩ := publication
  change producer = source at hOwner
  subst producer
  have hExact : Thread.Loader.recurringUseBefore X (source,index) =
      3 * ((Thread.Loader.atPrefix l X source arrival).published.countP
        (fun q => q.slot == slot)) + slot.val := by
    change (Thread.Loader.atPrefix l X source arrival).published.countP
      (fun q => q.slot == slot) = use/3 at hPhase
    rw [hUse, hPhase]
    change use = 3 * (use/3) + use%3
    omega
  obtain ⟨group, hMember⟩ :=
    Thread.Loader.copyMemberOfPublicationOfOccurrence hp hX he hVector hKind hPub hExact
  obtain ⟨pair, upper, hDst⟩ := group.destination hp hX hPub hMember
  dsimp only at hDst
  rw [group.slotFor hp hX hPub] at hDst
  change source = Thread.Loader.producer l (source/l.block) lane at hLane
  have hMod : (source%l.block)%64 = lane.val := by rw [hLane, Thread.Loader.producerLaneMod hp]
  have hAddress : kvCopyAddress l.sharedBase slot (source%l.block) pair upper =
      kvCopyAddress l.sharedBase slot lane pair upper := by
    simp only [kvCopyAddress, hMod, Nat.mod_eq_of_lt lane.isLt]
  rw [hAddress] at hDst
  let base := kvCopyAddress l.sharedBase slot lane pair upper
  change spec.dst = {loc := ⟨.shared,source/l.block,base⟩, size := 16} at hDst
  have h := hDst ▸ hCovers
  obtain ⟨hSpace, hCta', hLo, hHi⟩ := h
  have hLow : base ≤ loc.addr := hLo
  have hHigh : loc.addr < base + 16 := hHi
  let offset := loc.addr - base
  refine ⟨lane,pair,upper,offset,by dsimp [offset]; omega,?_⟩
  have hCta' : loc.cta = wait.1 / l.block := hCta'.trans hCta
  have hAddr : loc.addr = base + offset := by dsimp only [offset]; omega
  cases loc
  simp only [Loc.mk.injEq]
  exact ⟨hSpace,hCta',hAddr⟩

end LoaderReady

end PTX.Kernels.TmlFa4Fwd.Protocol
