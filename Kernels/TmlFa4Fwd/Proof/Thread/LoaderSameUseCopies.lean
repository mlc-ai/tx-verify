-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingEarlier
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyExit
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader
  (copyCommitPc primingPacketSite recurringPacketSite reuseArrival packetPlanePc)

private theorem recurringCopyPc {e : Event} (h : recurringVectorEvent e) : 909 ≤ e.pc := by
  obtain ⟨site,pair,upper,_,rfl⟩ := h
  change 909 ≤ packetPlanePc (recurringPacketSite site) pair upper
  fin_cases site <;> fin_cases pair <;> cases upper <;> decide

private theorem publicationBetweenOverlappingCopies {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i j : Nat} {e f : Event} (hi : X.get (g,i) = some e) (hj : X.get (g,j) = some f)
    (hFirst : recurringVectorEvent e) (hLater : recurringVectorEvent f)
    {s t : Spec} (hs : e.kind = .copy s) (ht : f.kind = .copy t)
    {loc : Loc} (hCover : s.dst.Covers loc) (hOther : t.dst.Covers loc)
    (hOrder : i < j) :
    ∃ k e, i < k ∧ k < j ∧ X.get (g,k) = some e ∧ recurringPublicationMark e = true := by
  have ha := actualCopyOfRecurringVector hi hFirst hs
  have hb := actualCopyOfRecurringVector hj hLater ht
  obtain ⟨hSeparate,_⟩ := overlappingCopiesSeparateGroups hp hX ha hb hCover hOther
  have hCommit : ∃ k, i < k ∧ k < j ∧ ∃ pc, X.get (g,k) = some ⟨pc,.asyncCommit⟩ := by
    by_contra! hNo
    apply hSeparate
    refine ⟨⟨s,ha,(actualCopyShape hX ha).completion⟩,⟨t,hb,(actualCopyShape hX hb).completion⟩,
      rfl,hOrder,?_⟩
    intro k pc hLo hHi hGet
    exact hNo k hLo hHi pc hGet
  have hLower := recurringCopyPc hFirst
  obtain ⟨site,k,target,hEarlier,hK,hEnd,hGet⟩ := copyPublicationBeforeSeparatelyCommittedCopy hX
    (show X.get (g,i) = some ⟨e.pc,.copy s⟩ by cases e; cases hs; exact hi)
    (show X.get (g,j) = some ⟨f.pc,.copy t⟩ by cases f; cases ht; exact hj)
    hOrder hCommit
  have hSiteValue : 2 ≤ site.val := by
    by_contra! hSmall
    let stage : Fin 2 := ⟨site.val,hSmall⟩
    have hSite : site = primingPacketSite stage := Fin.ext rfl
    rw [hSite] at hEnd
    have hEarlyAll : ∀ stage : Fin 2, copyCommitPc (primingPacketSite stage) < 909 := by decide
    have hEarly := hEarlyAll stage
    omega
  let stage : Fin 4 := ⟨site.val-2,by have := site.isLt; omega⟩
  have hSite : site = recurringPacketSite stage := Fin.ext (by
    change site.val = (site.val-2)+2
    omega)
  rw [hSite] at hGet
  exact ⟨k,_,hEarlier,hK,hGet,(recurringPublicationMark_iff _).2 ⟨stage,target,rfl⟩⟩

/-- Two actual overlapping copies at the same logical recurring use identify
one occurrence, even while that packet has no recorded publication. -/
theorem overlappingPendingCopiesOfSameUse {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {a b : EvId} {e f : Event} (he : X.get a = some e) (hf : X.get b = some f)
    (hA : recurringVectorEvent e) (hB : recurringVectorEvent f) {s t : Spec}
    (hs : e.kind = .copy s) (ht : f.kind = .copy t) {loc : Loc}
    (hCover : s.dst.Covers loc) (hOther : t.dst.Covers loc)
    (hUse : recurringUseBefore X a = recurringUseBefore X b) : a = b := by
  obtain ⟨g,i⟩ := a
  obtain ⟨g',j⟩ := b
  have hSame := (overlappingCopiesSameDestination hp hX
    (actualCopyOfRecurringVector he hA hs) (actualCopyOfRecurringVector hf hB ht)
    hCover hOther).1
  change g = g' at hSame
  subst g'
  have hStrict {i j : Nat} {e f : Event}
      (he : X.get (g,i) = some e) (hf : X.get (g,j) = some f)
      (hA : recurringVectorEvent e) (hB : recurringVectorEvent f)
      {s t : Spec} (hs : e.kind = .copy s) (ht : f.kind = .copy t)
      (hCover : s.dst.Covers loc) (hOther : t.dst.Covers loc)
      (hOrder : i < j) : recurringUseBefore X (g,i) < recurringUseBefore X (g,j) := by
    obtain ⟨k,event,hBefore,hK,hGet,hMark⟩ := publicationBetweenOverlappingCopies hp hX
      he hf hA hB hs ht hCover hOther hOrder
    have hLo := countP_take_mono recurringPublicationMark (X.tr g) hBefore.le
    have hHi := countP_take_mono recurringPublicationMark (X.tr g) (show k+1 ≤ j by omega)
    rw [countP_take_succ hGet hMark] at hHi
    change 2 + ((X.tr g).take i).countP recurringPublicationMark <
      2 + ((X.tr g).take j).countP recurringPublicationMark
    omega
  rcases lt_trichotomy i j with hLt | rfl | hGt
  · exact (Nat.ne_of_lt (hStrict he hf hA hB hs ht hCover hOther hLt) hUse).elim
  · rfl
  · exact (Nat.ne_of_gt (hStrict hf he hB hA ht hs hOther hCover hGt) hUse).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
