-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocConsistent
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.SnocReady

@[expose] public section

/-! Appending one event of any kind, including a warp-collective `tcgen05` event. The appended
event is the last of its thread, so it returns only once a later event follows; the thread's
previous last event must be ready (`LastReady`). The caller supplies the event-specific memory,
visibility, waiting and metadata facts. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- Appending a step of thread `g`, of any kind, whose visibility into every old node is
unchanged. -/
theorem consistent_snoc_last {t t1 : TState} {o : Option TState}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    (hnew : Returned (X.snoc g e r) (X.newId g) → Ready L (X.snoc g e r) (X.newId g))
    (hread : ∀ v a bs, (X.snoc g e r).MemReads v a bs → X.MemReads v a bs)
    (hwrite : ∀ v a bs, (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs)
    (hvis : ∀ l v f, X.RefPresent f →
        (modelCausality L (X.snoc g e r) l v f ↔ modelCausality L X l v f))
    (horder : OrderOk L K A (X.snoc g e r)) (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hextra : ExtensionObligations L A (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) := by
  apply consistent_preserving_extension hX le_snoc
  · intro h hh
    by_cases hhg : h = g
    · subst hhg
      exact ⟨o, by rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he⟩
    · rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
  · intro h hh
    rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh
  · exact hread
  · exact fun v a bs => (hwrite v a bs).mp
  · exact fun v a bs => (hwrite v a bs).mpr
  · exact fun v a bs hv k => le_snoc.2.1 v k ⟨a, bs, hread v a bs hv⟩
  · exact hvis
  · exact ready_snocHistory (records := X.objects) hX SnocRecords.same hexit hlast hnew
  · exact snoc_shflOk hX.shfl hns
  · exact horder
  · exact hasm
  · exact htma
  · rfl
  · exact hextra

/-- A warp-collective `tcgen05` event issues and awaits no asynchronous operation. -/
theorem asyncSilent_of_tcColl (hcoll : isTcColl e = true) : e.kind.AsyncSilent := by
  obtain ⟨pc, k⟩ := e
  cases k with
  | tc t => cases t <;> trivial
  | _ => simp [isTcColl] at hcoll

/-- A warp-collective `tcgen05` event returns once a later event of its thread exists, so the
appended one has not returned. -/
theorem not_returned_new_of_tcColl (hcoll : isTcColl e = true) :
    ¬ Returned (X.snoc g e r) (X.newId g) := by
  have hlen : ¬ (X.newId g).2 + 1 < ((X.snoc g e r).tr (X.newId g).1).length := by
    simp [snoc_len]
  intro h
  unfold Returned at h
  rw [snoc_get_new] at h
  obtain ⟨pc, k⟩ := e
  cases k with
  | tc t => cases t <;> first | exact hlen h | simp [isTcColl] at hcoll
  | _ => simp [isTcColl] at hcoll

/-- Appending a warp-collective tensor-core instruction, given the execution-order axioms of
the extension. -/
theorem consistent_tccoll_snoc_of_orderOk {t t1 : TState} {o : Option TState}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hcoll : isTcColl e = true) (hlast : LastReady L X g)
    (horder : OrderOk L K A (X.snoc g e r)) (hextra : ExtensionObligations L A (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r)) (htma : TmaOk (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) := by
  have hs := asyncSilent_of_tcColl hcoll
  have kne : ∀ {k : Kind}, isTcColl ⟨e.pc, k⟩ = false → e.kind ≠ k := by
    intro k hk h
    obtain ⟨pc, k'⟩ := e
    simp only at h
    subst h
    rw [hcoll] at hk
    cases hk
  have hnb : ∀ id count mode, e.kind ≠ .bar id count mode := fun _ _ _ => kne rfl
  have hnr : ∀ a bs, e.kind ≠ .rd a bs := fun _ _ => kne rfl
  have hnw : ∀ a bs, e.kind ≠ .wr a bs := fun _ _ => kne rfl
  have hrmw : ∀ a old new, e.kind ≠ .rmw a old new := fun _ _ _ => kne rfl
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f) :=
    baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf)
      (fun _ _ => kne rfl) hnb (fun _ _ _ _ => kne rfl) (fun _ => kne rfl)
  have hmat : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    cases k <;> simp_all [isTcColl, isMatrix]
  exact consistent_snoc_last hX hg hrun hl he (fun _ _ _ _ _ _ => kne rfl)
    (fun h => by rw [hmat] at h; cases h) hlast
    (fun h => (not_returned_new_of_tcColl hcoll h).elim)
    (fun _ _ _ => (hs.snoc_memReads hnr hrmw).mp)
    (fun _ _ _ => hs.snoc_memWrites hnw hrmw)
    (fun _ _ _ hf => hs.modelCausality_snoc_old hbo
      (snoc_allocResultBefore_old_of_not_write hnw)
      (refPresent_issuer_lt hX.effectValidity hf))
    horder hasm htma hextra

end
end PTX
