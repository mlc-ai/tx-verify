-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyExit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPacketGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint
import Kernels.TmlFa4Fwd.Proof.LoaderPacketContinuity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader (packetEntrySeparatesCopies kvCopyVectorsApart)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A copy whose next group commit belongs to a known publication is one of
that publication's actual vectors, whether or not its thread has exited. -/
theorem copyMemberOfNextPublication (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {target : Loc} {spec : Spec} (hCopy : X.Copy (g,i) spec)
    (hPub : X.AsyncArrive (g,j) target true) (hCopyBefore : i < j - 1)
    (hNone : ∀ n, i < n → n < j - 1 → ∀ e, X.get (g,n) = some e → e.kind ≠ .asyncCommit) :
    ∃ group : PublishedCopyGroup l X (g,j), (i,spec) ∈ group.copies := by
  obtain ⟨group,site,first,hFirst,hPc⟩ := publishedCopyGroupWithEntry hp hX hPub
  refine ⟨group,(group.member i spec).mpr ⟨?_,?_,hCopy⟩⟩
  · by_contra! hEarlier
    obtain ⟨k,packet,hPrior,hSubsequent,hCommit⟩ :=
      packetEntrySeparatesCopies hX site hCopy hFirst hPc hEarlier
    have hClose := group.closesAt
    have hLimit : group.first ≤ group.commit := by
      cases hList : group.copies with
      | nil =>
        have hCount := group.count
        simp [hList] at hCount
      | cons vector rest =>
        obtain ⟨k,s⟩ := vector
        have hm : (k,s) ∈ group.copies := hList.symm ▸ List.mem_cons_self
        obtain ⟨hLo,hHi,_⟩ := (group.member k s).mp hm
        exact hLo.trans hHi.le
    exact hNone k hPrior (by dsimp at hClose; omega) _ hCommit rfl
  · have hClose := group.closesAt
    change group.commit + 1 = j at hClose
    change i < j - 1 at hCopyBefore
    omega

/-- The first publication after a copy on an exited lane contains that copy's actual issue. -/
theorem copyPublicationMemberAtExit (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy : EvId} {spec : Spec} (hCopy : X.Copy copy spec) (hExit : Thread.Exited X copy.1) :
    ∃ (publication : EvId) (target : Loc) (group : PublishedCopyGroup l X publication),
      publication.1 = copy.1 ∧ X.AsyncArrive publication target true ∧
      (copy.2,spec) ∈ group.copies := by
  obtain ⟨g,i⟩ := copy
  obtain ⟨⟨g',j⟩,target,hLane,hPub,_,hOrder,hNone⟩ := copyFirstPublicationAtExit hX hCopy hExit
  change g' = g at hLane
  subst g'
  obtain ⟨group,hMember⟩ := copyMemberOfNextPublication hp hX hCopy hPub hOrder hNone
  exact ⟨(g,j),target,group,rfl,hPub,hMember⟩

/-- Published ordinary cache vectors covering a common byte have the same physical slot. -/
theorem PublishedCopyGroup.overlappingReadySlot (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {a b : EvId} {target : Loc} {slot : Fin 3}
    {owner : Nat} (first : PublishedCopyGroup l X a) (second : PublishedCopyGroup l X b)
    (hFirst : X.AsyncArrive a (readyObject l owner slot) true)
    (hSecond : X.AsyncArrive b target true) {i j : Nat} {s t : Spec} {loc : Loc}
    (hi : (i,s) ∈ first.copies) (hj : (j,t) ∈ second.copies) (hCover : s.dst.Covers loc)
    (hOther : t.dst.Covers loc) :
    X.AsyncArrive b (readyObject l owner slot) true := by
  obtain ⟨pair,upper,hS⟩ := first.destination hp hX hFirst hi
  obtain ⟨pair',upper',hT⟩ := second.destination hp hX hSecond hj
  have hSlot := first.slotFor hp hX hFirst
  dsimp only at hS hT
  rw [hSlot] at hS
  rw [hS] at hCover
  rw [hT] at hOther
  have hEq : second.publication.slot = slot := by
    by_contra hNe
    have hVal : slot.val ≠ second.publication.slot.val := fun h => hNe (Fin.ext h.symm)
    have hApart := kvCopyVectorsApart hp.shared.1 (a := a.1 % l.block) (b := b.1 % l.block)
      (u := upper) (v := upper') pair.isLt pair'.isLt (.inl hVal)
    obtain ⟨_,_,hLo,hHi⟩ := hCover
    obtain ⟨_,_,hLo',hHi'⟩ := hOther
    dsimp at hLo hHi hLo' hHi'
    rcases hApart with h | h <;> omega
  obtain ⟨pc,he⟩ := hSecond
  obtain ⟨publication,_,hTarget,_⟩ := readyObservation hp hX he rfl
  have hActual : X.AsyncArrive b (readyObject l b.1 publication.slot) true := hTarget ▸ ⟨pc,he⟩
  rw [← second.slotFor hp hX hActual,hEq] at hActual
  have hA : loc.cta = a.1/l.block := hCover.2.1
  have hB : loc.cta = b.1/l.block := hOther.2.1
  have hCta : owner/l.block = b.1/l.block := by
    obtain ⟨_,ha⟩ := hFirst
    obtain ⟨_,_,hAt,_⟩ := readyObservation hp hX ha rfl
    exact (congrArg Loc.cta hAt).trans (hA.symm.trans hB)
  simpa only [readyObject,hCta] using hActual

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
