-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaSource
public import Core.Tc.TcMmaConflicts
import Lemmas.Execution.ShapeExecution

@[expose] public section

namespace PTX.TcMma
open PTX PTX.Proof

private theorem listMaximal {α : Type} {r : α → α → Prop}
    (hIrrefl : ∀ a, ¬ r a a) (hTrans : ∀ {a b c}, r a b → r b c → r a c)
    (xs : List α) (hNonempty : xs ≠ []) :
    ∃ a ∈ xs, ∀ b ∈ xs, ¬ r a b := by
  classical
  induction xs with
  | nil => exact (hNonempty rfl).elim
  | cons a xs ih =>
    by_cases hEmpty : xs = []
    · subst xs
      exact ⟨a,by simp,fun b hb => (List.mem_singleton.mp hb).symm ▸ hIrrefl a⟩
    obtain ⟨c,hc,hMax⟩ := ih hEmpty
    by_cases hNext : r c a
    · refine ⟨a,List.mem_cons_self,fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hIrrefl _
      · exact fun hab => hMax b hb (hTrans hNext hab)
    · refine ⟨c,List.mem_cons_of_mem _ hc,fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hNext
      · exact hMax b hb

private theorem tmemWrite_thread_lt {L : Launch} {X : Execution} {K : Kernel}
    {A : List Assumption} {m : Mem0} (hX : Consistent L K A m X)
    {i : EvId} {cell : Cell} (h : TmemWrite L X i cell) : i.1 < L.threads := by
  rcases h with ⟨_,_,_,_,_,_,⟨_,he⟩,_⟩ | ⟨_,_,_,_,⟨_,he⟩,_,_⟩ |
    ⟨_,_,_,_,⟨_,he⟩,_,_,_⟩ | ⟨_,⟨_,he⟩,_⟩ <;> exact event_thread_lt hX he

/-- Ordered writers and one write before a read provide a stable latest write.
The read must precede all covering releases, and its accesses must be ordered
with all competing writes. -/
theorem readSourceOfCandidate {L : Launch} {X : Execution} {K : Kernel}
    {A : List Assumption} {m : Mem0} (hX : Consistent L K A m X) (hGuard : SyncGuarded L K X)
    (hWrites : WritesSafe L X) {kind : TmemRead} {reader candidate : EvId} {cell : Cell}
    (hOrdered : ∀ w, TmemWrite L X w cell →
      WriteBefore L X w reader ∨ ReadBefore L X kind reader w)
    (hLive : ∀ w, TmemWrite L X w cell → WriteBefore L X w reader →
      SourceLive L X w reader cell)
    (hWrite : TmemWrite L X candidate cell) (hBefore : WriteBefore L X candidate reader) :
    ∃ latest, ReadSource L X kind latest reader cell := by
  classical
  let ids := (List.range L.threads).flatMap (fun g =>
    (List.range (X.tr g).length).map fun i => (g,i))
  let past := ids.filter (fun i => decide (TmemWrite L X i cell ∧ WriteBefore L X i reader))
  have hMember (i : EvId) (hI : TmemWrite L X i cell) (hB : WriteBefore L X i reader) :
      i ∈ past := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_flatMap.mpr ⟨i.1,List.mem_range.mpr (tmemWrite_thread_lt hX hI),?_⟩,?_⟩
    · exact List.mem_map.mpr ⟨i.2,List.mem_range.mpr (tmemWrite_lt hI),rfl⟩
    · exact decide_eq_true ⟨hI,hB⟩
  have hNonempty : past ≠ [] := List.ne_nil_of_mem (hMember candidate hWrite hBefore)
  have hIrrefl := tcStep_acyclic hX hGuard
  obtain ⟨source,hSource,hLast⟩ :=
    listMaximal hIrrefl (fun a b => a.trans b) past hNonempty
  obtain ⟨hW,hB⟩ := of_decide_eq_true (List.mem_filter.mp hSource).2
  have hNe : source ≠ reader := fun hEq => hIrrefl reader (hEq ▸ hB.tcStep)
  refine ⟨source,hNe,hW,hB,?_,hLive _ hW hB⟩
  intro w hw
  by_cases heq : w = source
  · exact .inl heq
  rcases hOrdered w hw with hPast | hFuture
  · rcases hWrites w source cell hw hW with hSame | hPrior | hLater
    · exact (heq hSame).elim
    · exact .inr (.inl hPrior)
    · exact (hLast w (hMember w hw hPast) hLater.tcStep).elim
  · exact .inr (.inr hFuture)

end PTX.TcMma
