-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingEarlier

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (PublishedCopyGroup readyObject recurringUseBefore recurringVectorEvent)

/-- A recorded recurring copy covering the same byte in the same logical use
is the same event as the vector selected from that generation's publication. -/
theorem overlappingRecurringCopyOfSameUse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index owner : Nat} {event : Event} (he : X.get (g,index) = some event)
    (hVector : recurringVectorEvent event) {other : Spec} (hKind : event.kind = .copy other)
    {publication : EvId} {slot : Fin 3}
    (hPub : X.AsyncArrive publication (readyObject l owner slot) true)
    (hUse : recurringUseBefore X (g,index) = 3 * generation l X publication slot + slot.val)
    (group : PublishedCopyGroup l X publication)
    {member : Nat} {selected : Spec} {loc : Loc} (hMember : (member,selected) ∈ group.copies)
    (hCover : selected.dst.Covers loc) (hOther : other.dst.Covers loc) :
    (g,index) = (publication.1,member) := by
  have hCopy := Thread.Loader.actualCopyOfRecurringVector he hVector hKind
  have hSelected := ((group.member member selected).mp hMember).2.2
  have hSame := (Thread.Loader.overlappingCopiesSameDestination hp hX hCopy hSelected
    hOther hCover).1
  obtain ⟨producer,i⟩ := publication
  change g = producer at hSame
  subst producer
  obtain ⟨otherGroup,hOldMember⟩ :=
    Thread.Loader.copyMemberOfPublicationOfOccurrence hp hX he hVector hKind hPub hUse
  exact Prod.ext rfl (coveringCopyUniqueInGeneration hp hX otherGroup group hPub hPub
    rfl hOldMember hMember hOther hCover).2

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
