-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.BarWaiting
public import Lemmas.Snoc.Collectives
public import Lemmas.Flow.Determinism
public import Lemmas.Snoc.SnocReady

@[expose] public section

/-!
# Appending a barrier arrival

The proof works with ordinary and independent async memory events and arbitrarily many
mbarrier phases. The arrival preserves old causality; independent effect and object-history
records are retained, and readiness holds when the thread's previous last event is ready. The
execution-order axioms transfer by the append frame (`snoc_bar_orderOk`).
There is no Fresh condition, no synthetic next-thread copy write, and no async-free hypothesis.
-/
namespace PTX
noncomputable section

/-- A thread's next barrier arrival extends any consistent execution whose thread's previous
last event is ready (`LastReady`). -/
theorem consistent_bar_snoc {L : Launch} {X : Execution} {g : Nat} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads) {t t1 : TState} {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {id : Nat} {count : Option Nat} (he : EStep K A L g t1 ⟨t1.pc, .bar id count⟩ o)
    (hlast : LastReady L X g)
    (hextra : ExtensionObligations L A (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none)))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none))) :
    Consistent L K A mem0 (X.snoc g ⟨t1.pc, .bar id count⟩ (fun _ => none)) := by
  let ev : Event := ⟨t1.pc, .bar id count⟩
  let r : Nat → Option AsyncCopy.Ref := fun _ => none
  show Consistent L K A mem0 (X.snoc g ev r)
  have hkind : ev.kind = .bar id count := rfl
  have hk : ev.kind.isTma = false := rfl
  have hns : ∀ m a b c recv ok, ev.kind ≠ .shfl m a b c recv ok := by simp [ev]
  have hrmw : ∀ a old new, ev.kind ≠ .rmw a old new := by simp [ev]
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g ev r) x f ↔ baseCausality L X x
          f) := baseCausality_snoc_old_bar hX.cluster hX.rf hX.ctaBar hg hk
  have htma : TmaOk (X.snoc g ev r) := tmaOk_snoc_plain hX.tma hk
  have hnew : ¬ Returned (X.snoc g ev r) (X.newId g) := by
    unfold Returned
    rw [snoc_get_new]
    simp [ev, Kind.resume, snoc_len]
  apply consistent_preserving_extension hX le_snoc
  · intro h hh
    by_cases hhg : h = g
    · subst hhg
      refine ⟨o, ?_⟩
      rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he
    · rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
  · intro h hh
    rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh
  · intro v a bs hv
    exact (snoc_memReads hk (by simp [ev]) hrmw).mp hv
  · intro v a bs hv
    exact (snoc_memWrites hk (by simp [ev]) hrmw).mp hv
  · intro v a bs hv
    exact (snoc_memWrites hk (by simp [ev]) hrmw).mpr hv
  · intro v a bs hv k
    have hold := (snoc_memReads hk (by simp [ev]) hrmw).mp hv
    exact (le_snoc (X := X) (g := g) (e := ev) (r := r)).2.1 v k ⟨a, bs, hold⟩
  · intro l x f hf
    exact modelCausality_snoc_old hk hbo (snoc_allocResultBefore_old hX.dependency.ready)
      (refPresent_issuer_lt hX.effectValidity hf)
  · exact ready_snocHistory (records := X.objects) hX SnocRecords.same (fun h => by cases h)
      hlast (fun h => (hnew h).elim)
  · exact snoc_shflOk hX.shfl hns
  · exact snoc_bar_orderOk hX hkind
  · exact hasm
  · exact htma
  · rfl
  · exact hextra

end
end PTX
