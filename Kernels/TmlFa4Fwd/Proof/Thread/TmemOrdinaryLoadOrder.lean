-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemLoadCompletion
import Lemmas.Order.OrderBaseCausality
import Lemmas.Execution.ShapeExecution
import Lemmas.Flow.PollRounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.TcMma PTX.Proof

/-- Ordinary Tensor Memory loads and stores of one physical lane are pipeline-ordered. -/
theorem tensorLoadStoreOrderedOnThread {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {load store : EvId}
    (hLoad : ∃ address words shape, X.TLd load address words shape)
    (hStore : ∃ address words shape, X.TSt store address words shape)
    (hLane : store.1 = load.1) : WriteBefore l X store load ∨ ReadBefore l X .ld load store := by
  have hL := hLoad
  obtain ⟨_,_,_,_,hRead⟩ := hL
  have hS := hStore
  obtain ⟨_,_,_,_,hWrite⟩ := hS
  have hCta := congrArg (· / l.block) hLane
  have hWarp : SameWarp l store.1 load.1 :=
    ⟨⟨event_thread_lt hX hWrite,event_thread_lt hX hRead,hCta⟩,by rw [hLane]⟩
  rcases lt_trichotomy store.2 load.2 with hPast | hEqual | hFuture
  · have hPo := po_of_not_access hLane hPast (len_of_get hRead) (by rw [hRead]; rfl)
    exact .inl (.inr (.inl ⟨hStore,.inr (.inl ⟨hWarp,.inl (.single (.inl hPo)),hStore,hLoad⟩)⟩))
  · rw [Prod.ext hLane hEqual,hRead] at hWrite
    exact False.elim
      (TcKind.noConfusion (Kind.tc.inj (congrArg Event.kind (Option.some.inj hWrite))))
  · have hPo := po_of_not_access hLane.symm hFuture (len_of_get hWrite) (by rw [hWrite]; rfl)
    exact .inr (.inr ⟨hWarp.symm,.inl (.single (.inl hPo)),hLoad,hStore⟩)

/-- The actual implicit wait of a dataflow load precedes a subsequent
non-wait event on its lane, and every consumer reached by that event. -/
theorem dataflowLoadWaitThroughEvent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {load later consumer : EvId}
    (hLoad : DataflowLoad X load) {event : Event} (he : X.get later = some event)
    (hBefore : TraceBefore X load later) (hNotWait : event.kind ≠ .tc .waitLd)
    (hCausal : baseCausality l X later consumer) : WaitBefore l X .waitLd load consumer := by
  obtain ⟨g,i⟩ := load
  obtain ⟨g',j⟩ := later
  have hLane : g = g' := hBefore.1
  subst g'
  have hLength : j < (X.tr g).length := len_of_get he
  have hPast : i+1 ≤ j := hBefore.2.1
  obtain ⟨site,hWait⟩ := dataflowLoadWait hX hLoad (hPast.trans_lt hLength)
  have hj : i+1 < j := by
    rcases Nat.eq_or_lt_of_le hPast with hEq | hLt
    · have hSame := Option.some.inj (he.symm.trans (hEq ▸ hWait))
      exact (hNotWait (congrArg Event.kind hSame)).elim
    · exact hLt
  have hPo := po_of_source_not_access (e := (g,i+1)) (f := (g,j)) rfl hj hLength
    (by rw [hWait]; rfl)
  exact ⟨(g,i+1),⟨site,hWait⟩,rfl,by omega,
    .inl ((Relation.TransGen.single (.inl hPo)).trans hCausal)⟩

end PTX.Kernels.TmlFa4Fwd.Thread
