-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncChain
public import Lemmas.Snoc.SnocObjectMemory
public import Lemmas.Snoc.SnocVisibility
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.SnocAsync
public import Lemmas.Snoc.SnocOrder
public import Lemmas.Snoc.SnocAsyncSilent

@[expose] public section

/-! Appending a control event — a proxy fence or a cluster-barrier operation — changes no
memory access, async issue, observation or happens-before edge into an existing event.
Hence every visibility relation into existing references is unchanged. -/

namespace PTX
open AsyncCopy
noncomputable section

/-- A proxy fence, an mbarrier-initialization fence or a cluster-barrier operation. -/
def Kind.Control (k : Kind) : Prop :=
  (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ ∃ op, k = .cluster op

namespace Control
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}
  {K : Kernel} {A : List Assumption} {mem0 : Mem0}

private theorem ne {k : Kind} (hc : e.kind.Control) (hk : ¬ k.Control) : e.kind ≠ k := by
  intro h; exact hk (h ▸ hc)

theorem not_tc (hc : e.kind.Control) (k : TcKind) : e.kind ≠ .tc k :=
  ne hc (by rintro (⟨_, _, h⟩ | h | ⟨_, h⟩) <;> cases h)

private theorem cases_kind (hc : e.kind.Control) {k : Kind}
    (hk : ∀ f s, k ≠ .fenceProxy f s) (hm : k ≠ .fenceMbarInit) (hk' : ∀ op, k ≠ .cluster op) :
    e.kind ≠ k :=
  ne hc (by rintro (⟨f, s, h⟩ | h | ⟨op, h⟩); exact hk f s h; exact hm h; exact hk' op h)

macro "control_ne" hc:term : term =>
  `(cases_kind $hc (by intro _ _ h; cases h) (by intro h; cases h) (by intro _ h; cases h))

/-- A control event issues and awaits no asynchronous operation. -/
theorem asyncSilent (hc : e.kind.Control) : e.kind.AsyncSilent := by
  rcases hc with ⟨f, s, h⟩ | h | ⟨op, h⟩ <;> rw [h] <;> trivial

theorem memReads (hc : e.kind.Control) (hX : Consistent L K A mem0 X) (i : Ref) (a : Acc)
    (bs : List (Option Byte)) : (X.snoc g e r).MemReads i a bs ↔ X.MemReads i a bs :=
  snoc_memReads_control hX.effectValidity (not_tc hc) (fun _ _ => control_ne hc)
    (fun _ _ _ => control_ne hc)

theorem memWrites (hc : e.kind.Control) (hX : Consistent L K A mem0 X) (i : Ref) (a : Acc)
    (bs : List Byte) : (X.snoc g e r).MemWrites i a bs ↔ X.MemWrites i a bs :=
  snoc_memWrites_control hX.effectValidity (fun _ _ => control_ne hc) (fun _ _ _ => control_ne hc)

theorem baseCausality_old (hc : e.kind.Control) (hX : Consistent L K A mem0 X) {i j : EvId}
    (hj : j.2 < (X.tr j.1).length) : baseCausality L (X.snoc g e r) i j ↔ baseCausality L X i j :=
  baseCausality_snoc_old_of_not_arrive hX.cluster
    (.of_noWrite (fun _ _ => control_ne hc) (fun _ _ _ => control_ne hc))
    (fun _ _ => control_ne hc) (fun _ _ _ => control_ne hc)
    (fun _ _ _ _ => control_ne hc) (fun _ => control_ne hc) hj

theorem asyncCovers (hc : e.kind.Control) (i : EvId) (p : Part) (l : Loc) :
    AsyncCovers (X.snoc g e r) i p l ↔ AsyncCovers X i p l :=
  (asyncSilent hc).snoc_asyncCovers

theorem asyncFinished (hc : e.kind.Control) (i : EvId) (p : Part) (w : EvId) :
    AsyncFinished L (X.snoc g e r) i p w ↔ AsyncFinished L X i p w :=
  (asyncSilent hc).snoc_asyncFinished

theorem asyncOnlyFinished (hc : e.kind.Control) (i : EvId) (p : Part) (w : EvId) :
    AsyncOnlyFinished (X.snoc g e r) i p w ↔ AsyncOnlyFinished X i p w := by
  simp only [AsyncOnlyFinished, (asyncSilent hc).snoc_asyncPresent,
    (asyncSilent hc).snoc_groupWaitsFor, (asyncSilent hc).snoc_groupWaitStages]

private theorem po_old {e' f : EvId} (hf : f.2 < (X.tr f.1).length) :
    po (X.snoc g e r) e' f ↔ po X e' f := by
  exact po_snoc_old hf

theorem proxyBefore (hc : e.kind.Control) (hX : Consistent L K A mem0 X) (e' i : EvId) (l : Loc)
    (hi : i.2 < (X.tr i.1).length) :
    ProxyBefore L (X.snoc g e r) e' i l ↔ ProxyBefore L X e' i l :=
  Kind.AsyncSilent.proxyBefore_snoc_old (fun hf => baseCausality_old hc hX hf) hi

theorem asyncBefore (hc : e.kind.Control) (hX : Consistent L K A mem0 X) (l : Loc)
    (a b : EvId × Part) : AsyncBefore L (X.snoc g e r) l a b ↔ AsyncBefore L X l a b :=
  AsyncBefore.congr (fun _ _ => asyncCovers hc ..) (fun _ _ _ => asyncFinished hc ..)
    (fun _ _ _ => asyncOnlyFinished hc ..) (fun _ _ _ h => baseCausality_old hc hX h.issuer_lt)
    (fun _ _ _ h => po_old h.issuer_lt)

theorem modelCausality (hc : e.kind.Control) (hX : Consistent L K A mem0 X) (l : Loc) (e' f : Ref)
    (hf : X.RefPresent f) : modelCausality L (X.snoc g e r) l e' f ↔ modelCausality L X l e' f :=
  (asyncSilent hc).modelCausality_snoc_old (fun hb => baseCausality_old hc hX hb)
    (snoc_allocResultBefore_old hX.dependency.ready)
    (refPresent_issuer_lt hX.effectValidity hf)

end Control
end
end PTX
