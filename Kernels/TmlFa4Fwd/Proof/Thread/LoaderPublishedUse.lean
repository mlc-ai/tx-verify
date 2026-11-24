-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Loader (reuseArrival actualReuseLastCopy)

private theorem beforeRecurringArrival {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hMark : recurringPublicationMark e = true) :
    ∃ (copy : Nat) (spec : AsyncCopy.Spec) (commit : Event),
      copy+2 = index ∧ X.Copy (g,copy) spec ∧ X.get (g,copy+1) = some commit ∧
      commit.kind = .asyncCommit := by
  obtain ⟨site,loc,rfl⟩ := (recurringPublicationMark_iff e).mp hMark
  obtain ⟨copy,spec,hId,hCopy,_,hCommit⟩ := actualReuseLastCopy hp hX site he
  exact ⟨copy,spec,_,hId,hCopy,hCommit,rfl⟩

/-- Every copy in a recurring published packet has the same logical use as its arrival. -/
theorem PublishedCopyGroup.memberUse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication : Nat} (group : PublishedCopyGroup l X (g,publication))
    {e : Event} (he : X.get (g,publication) = some e)
    (hMark : recurringPublicationMark e = true)
    {i : Nat} {spec : AsyncCopy.Spec} (hMember : (i,spec) ∈ group.copies) :
    recurringUseBefore X (g,i) = recurringUseBefore X (g,publication) := by
  obtain ⟨last,lastSpec,commit,hIndex,hLast,hCommit,hKind⟩ :=
    beforeRecurringArrival hp hX he hMark
  obtain ⟨hFirst,hBefore,hCopy⟩ := (group.member i spec).mp hMember
  have hClose := group.closesAt
  change group.commit+1 = publication at hClose
  have hEnd : i ≤ last := by omega
  have hLastMember : (last,lastSpec) ∈ group.copies :=
    (group.member last lastSpec).mpr ⟨hFirst.trans hEnd,by omega,hLast⟩
  let rank := fun j => ((X.tr g).take j).countP recurringPublicationMark
  have hLe : rank i ≤ rank publication :=
    countP_take_mono recurringPublicationMark (X.tr g) (by omega)
  change 2+rank i = 2+rank publication
  congr 1
  apply Nat.le_antisymm hLe
  by_contra! hLt
  obtain ⟨k,event,hEarlier,hK,hEvent,hOrd⟩ :=
    exists_nthEv (X := X) (p := recurringPublicationMark) (g := g)
      (k := publication) (n := rank i) hLt
  have hi : i ≤ k := by
    by_contra! hBeforeCopy
    have hs := countP_take_succ (p := recurringPublicationMark) hK hEvent
    have hm := countP_take_mono recurringPublicationMark (X.tr g) (show k+1 ≤ i by omega)
    change rank (k+1) = rank k+1 at hs
    change rank (k+1) ≤ rank i at hm
    change rank k = rank i at hOrd
    omega
  obtain ⟨prior,_,priorCommit,hPrior,_,hPriorCommit,hPriorKind⟩ :=
    beforeRecurringArrival hp hX hK hEvent
  have hEventKind : ∃ target, event.kind = .asyncArrive target true := by
    obtain ⟨_,target,rfl⟩ := (recurringPublicationMark_iff event).mp hEvent
    exact ⟨target,rfl⟩
  have hiLt : i < prior+1 := by
    by_contra! hContra
    obtain ⟨_,hCopyEvt⟩ := hCopy
    by_cases hEq : i = k
    · rw [hEq,hK] at hCopyEvt
      obtain ⟨target,hTarget⟩ := hEventKind
      have := congrArg Event.kind (Option.some.inj hCopyEvt)
      rw [hTarget] at this
      cases this
    · have hEq : i = prior+1 := by omega
      rw [hEq,hPriorCommit] at hCopyEvt
      have := congrArg Event.kind (Option.some.inj hCopyEvt)
      rw [hPriorKind] at this
      cases this
  have hLastLt : prior+1 < last := by
    by_contra! hContra
    by_cases hEq : k = last+1
    · rw [hEq,hCommit] at hK
      obtain ⟨target,hTarget⟩ := hEventKind
      have := congrArg Event.kind (Option.some.inj hK)
      rw [hKind,hTarget] at this
      cases this
    · have hEq : k = last := by omega
      obtain ⟨_,hLastEvt⟩ := hLast
      rw [hEq,hLastEvt] at hK
      obtain ⟨target,hTarget⟩ := hEventKind
      have := congrArg Event.kind (Option.some.inj hK)
      rw [hTarget] at this
      cases this
  have hGroup := group.sameGroup hMember hLastMember (hiLt.trans hLastLt)
  have hPriorEvent : X.get (g,prior+1) = some ⟨priorCommit.pc,.asyncCommit⟩ := by
    rw [← hPriorKind]
    exact hPriorCommit
  exact hGroup.2.2.2.2 (prior+1) priorCommit.pc hiLt hLastLt hPriorEvent

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
