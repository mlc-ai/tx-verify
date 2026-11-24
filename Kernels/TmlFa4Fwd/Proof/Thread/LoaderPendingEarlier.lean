-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketPlane
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvEmptyPhase)

/-- Before an open packet's empty acquire, the same loader lane has issued
the ready publications for all earlier recurring uses. -/
theorem earlierPublicationBeforePendingCopyGuard {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {e : Event} (he : X.get (g,index) = some e)
    (hCopy : recurringVectorEvent e) :
    ∃ wait,
      let use := recurringUseBefore X (g,index)
      EmptyAcquire l X wait (kvUseStage use) (if kvEmptyPhase use then 1 else 0) ∧
      Resumes kernel X wait (g,index) ∧
      ∀ earlier, 2 ≤ earlier → earlier < use →
        ∃ j, TraceBefore X (g,j) wait ∧
          X.AsyncArrive (g,j) (readyObject l g (kvUseStage earlier)) true ∧
          (atPrefix l X g j).published.countP (fun pub => pub.slot == kvUseStage earlier) =
            earlier/3 := by
  obtain ⟨start,pre,wait,hStart,_,hEmpty,hResume,_,hUse,site,n,rfl,hGuard⟩ :=
    actualVectorUseWithGuardPrefix hp hX he hCopy
  let stop := start + (pre.length + n)
  let front := pre ++ List.replicate n
    (cursorPoll l g (2 + pre.countP recurringPublicationMark) site false)
  let last := cursorPoll l g (2 + pre.countP recurringPublicationMark) site true
  change ((X.tr g).drop start).take (stop - start + 1) = front ++ [last] at hGuard
  have hLen : ((X.tr g).take start).length = start := by
    rw [List.length_take,Nat.min_eq_left]
    exact hStart.trans (len_of_get he).le
  have hSize : (((X.tr g).take start) ++ front).length = stop := by
    simp [front,stop,hLen]
  have hCut : (X.tr g).take (stop+1) = ((X.tr g).take start ++ front) ++ [last] := by
    conv_lhs => rw [show stop + 1 = start + (stop - start + 1) by
      dsimp only [stop]; omega]
    rw [List.take_add,hGuard]
    simp [List.append_assoc,front]
  have hPrefix : (X.tr g).take stop = (X.tr g).take start ++ front := by
    rw [← Nat.min_eq_left (Nat.le_succ stop),← List.take_take,hCut]
    nth_rw 1 [← hSize]
    rw [List.take_left]
  have hCount : pre.countP recurringPublicationMark ≤
      ((X.tr g).take stop).countP recurringPublicationMark := by
    rw [hPrefix]
    simp only [front,List.countP_append]
    omega
  refine ⟨(g,stop),hUse ▸ hEmpty,hResume,?_⟩
  intro earlier hTwo hBefore
  obtain ⟨j,hLt,v,hj,hMark,hRank⟩ :=
    exists_nth recurringPublicationMark (X.tr g) (k := stop) (n := earlier-2) (by omega)
  have hRank' : recurringUseBefore X (g,j) = earlier := by
    change 2 + ((X.tr g).take j).countP recurringPublicationMark = earlier
    omega
  obtain ⟨hPublished,hOrdinal⟩ := recurringPublicationAtUse hp hX hj hMark
  rw [hRank'] at hPublished hOrdinal
  exact ⟨j,⟨rfl,hLt,(hResume.1.2.1.trans hResume.1.2.2)⟩,hPublished,hOrdinal⟩

/-- An actual recurring vector event issues its ordinary copy. -/
theorem actualCopyOfRecurringVector {X : Execution} {i : EvId} {e : Event}
    (he : X.get i = some e) (hVector : recurringVectorEvent e)
    {spec : AsyncCopy.Spec} (hKind : e.kind = .copy spec) : X.Copy i spec := by
  obtain ⟨_,_,_,copy,rfl⟩ := hVector
  obtain rfl := Kind.copy.inj hKind
  exact ⟨_,he⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
