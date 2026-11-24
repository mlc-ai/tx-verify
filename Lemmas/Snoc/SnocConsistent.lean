-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.Collectives
public import Lemmas.Flow.Determinism
public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.Snoc.SnocPlainWaiting
public import Lemmas.Snoc.ControlFrame
public import Lemmas.Snoc.SnocReady

@[expose] public section

/-! Appending one event to one thread. The source trace and shuffle values of the prefix carry
over, and readiness holds when the thread's previous last event is ready (`LastReady`). The
caller supplies the event-specific memory, visibility, waiting and metadata facts. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

namespace Control

theorem waitFree (hc : e.kind.Control) : e.kind.WaitFree := by
  obtain ⟨pc, k⟩ := e
  refine ⟨?_, not_tc hc⟩
  rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> simp only at h <;> subst h <;> trivial

theorem not_bar (hc : e.kind.Control) : ∀ id count mode, e.kind ≠ .bar id count mode := by
  intro _ _ _; rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> rw [h] <;> intro h' <;> cases h'

theorem not_shfl (hc : e.kind.Control) : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok := by
  intros; rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> rw [h] <;> intro h' <;> cases h'

/-- A control event adds no waiting edge out of an existing event. -/
theorem orderOk (hc : e.kind.Control) (hX : Consistent L K A mem0 X) :
    OrderOk L K A (X.snoc g e r) := by
  have hm : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> simp only at h <;> subst h <;> rfl
  refine snoc_plain_orderOk hX (waitFree hc) (not_shfl hc) ?_ ?_ hm ?_ ?_ <;>
    rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> simp_all [Kind.laneValue]

end Control

section
variable {t t1 : TState} {o : Option TState}

private theorem snoc_threads (hX : Consistent L K A mem0 X)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) : ∀ h < L.threads, Produces K A L h ((X.snoc g e r).tr h) := by
  intro h hh
  by_cases hhg : h = g
  · subst hhg
    exact ⟨o, by rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he⟩
  · rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh

private theorem snoc_outside (hX : Consistent L K A mem0 X) (hg : g < L.threads) :
    ∀ h, L.threads ≤ h → (X.snoc g e r).tr h = [] := by
  intro h hh
  rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh

/-- Appending a step of thread `g` retains visibility between old present nodes. -/
theorem consistent_snoc_preserving_present (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    (hnew : Returned (X.snoc g e r) (X.newId g) → Ready L (X.snoc g e r) (X.newId g))
    (hread : ∀ v a bs, (X.snoc g e r).MemReads v a bs → X.MemReads v a bs)
    (hwrite : ∀ v a bs, (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs)
    (hvis : ∀ l v f, X.RefPresent v → X.RefPresent f →
      (modelCausality L (X.snoc g e r) l v f ↔ modelCausality L X l v f))
    (horder : OrderOk L K A (X.snoc g e r)) (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hextra : ExtensionObligations L A (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_preserving_present_extension hX le_snoc (snoc_threads hX hrun hl he)
    (snoc_outside hX hg) hread
    (fun v a bs => (hwrite v a bs).mp) (fun v a bs => (hwrite v a bs).mpr)
    (fun v a bs hv k => le_snoc.2.1 v k ⟨a, bs, hread v a bs hv⟩) hvis
    (ready_snocHistory (records := X.objects) hX SnocRecords.same hexit hlast hnew)
    (snoc_shflOk hX.shfl hns) horder hasm htma rfl hextra

/-- Appending a step of thread `g` whose visibility into every old node is unchanged. -/
theorem consistent_snoc_preserving (hX : Consistent L K A mem0 X) (hg : g < L.threads)
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
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_snoc_preserving_present hX hg hrun hl he hns hexit hlast hnew hread hwrite
    (fun loc v f _ hf => hvis loc v f hf) horder hasm htma hextra

/-- Appending a step of thread `g` that only grows visibility, when the conflicts at the bytes
that are read are ordered and the step orders no two old same-value writes that `X` leaves
unordered. -/
theorem consistent_snoc_collective_reads (hX : Consistent L K A mem0 X)
    (hord : ReadsOrdered L X) (hg : g < L.threads)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    (hnew : Returned (X.snoc g e r) (X.newId g) → Ready L (X.snoc g e r) (X.newId g))
    (hread : ∀ v a bs, (X.snoc g e r).MemReads v a bs → X.MemReads v a bs)
    (hwrite : ∀ v a bs, (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs)
    (hmono : ∀ l v f, modelCausality L X l v f → modelCausality L (X.snoc g e r) l v f)
    (hsame : ∀ l v f a b, SameValueWrites X v f a b → X.RefPresent v → X.RefPresent f →
      ByteCausality L (X.snoc g e r) l v f → ByteCausality L X l v f)
    (horder : OrderOk L K A (X.snoc g e r)) (hsg : SyncGuarded L K (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hextra : ExtensionObligations L A (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_collective_extension_reads hX le_snoc hord (snoc_threads hX hrun hl he)
    (snoc_outside hX hg) hread
    (fun v a bs => (hwrite v a bs).mp) (fun v a bs => (hwrite v a bs).mpr)
    (fun v a bs hv k => le_snoc.2.1 v k ⟨a, bs, hread v a bs hv⟩) hmono hsame
    (ready_snocHistory (records := X.objects) hX SnocRecords.same hexit hlast hnew)
    (snoc_shflOk hX.shfl hns) horder hsg hasm htma rfl hextra

/-- Appending a step of thread `g` that only grows visibility, in a race-free prefix. -/
theorem consistent_snoc_collective (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X)
    (hr : ¬ Race L X) (hst : StrongOrdered L X) (hg : g < L.threads)
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o)
    (hns : ∀ m a b c recv ok, e.kind ≠ .shfl m a b c recv ok)
    (hexit : isMatrix e = true → ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hlast : LastReady L X g)
    (hnew : Returned (X.snoc g e r) (X.newId g) → Ready L (X.snoc g e r) (X.newId g))
    (hread : ∀ v a bs, (X.snoc g e r).MemReads v a bs → X.MemReads v a bs)
    (hwrite : ∀ v a bs, (X.snoc g e r).MemWrites v a bs ↔ X.MemWrites v a bs)
    (hmono : ∀ l v f, modelCausality L X l v f → modelCausality L (X.snoc g e r) l v f)
    (hsame : ∀ l v f a b, SameValueWrites X v f a b → X.RefPresent v → X.RefPresent f →
      ByteCausality L (X.snoc g e r) l v f → ByteCausality L X l v f)
    (horder : OrderOk L K A (X.snoc g e r)) (hsg : SyncGuarded L K (X.snoc g e r))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g e r))
    (htma : TmaOk (X.snoc g e r)) (hextra : ExtensionObligations L A (X.snoc g e r)) :
    Consistent L K A mem0 (X.snoc g e r) :=
  consistent_snoc_collective_reads hX (.of_safe hm hr hst) hg hrun hl he hns hexit hlast hnew
    hread hwrite hmono hsame horder hsg hasm htma hextra

end
end
end PTX
