-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncOrder
public import Lemmas.Order.GuardObserver

@[expose] public section

/-! # Byte visibility has no cycle

Byte visibility composes through a thread instruction (causality before and after it, or a
completion observed by a wait causally before it), and through an asynchronous effect between
two asynchronous effects (`AsyncChain.trans`). Along a cycle that meets an asynchronous effect
`a`, the visibility from `a` therefore reaches an asynchronous node `b` with `a` visible to `b`
and `b` visible to `a` (or `a` visible to itself), which `modelCausality_asymm_guarded` excludes
under guarded synchronization. A cycle of thread instructions is a causality cycle. -/

namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {K : Kernel} {X : Execution} {l : Loc}

/-- Wide visibility composes through a thread instruction. -/
theorem ModelCausalityChain.trans_thread {e g : Ref} {f : EvId}
    (h1 : ModelCausalityChain L X l e (.thread f))
    (h2 : ModelCausalityChain L X l (.thread f) g) : ModelCausalityChain L X l e g := by
  cases e with
  | thread e =>
    cases g with
    | thread g => exact Relation.TransGen.trans h1 h2
    | async j q =>
      obtain ⟨hc, ⟨fence, sp, sc, hf, hlt, hcl, hcta, ha, hb⟩ | ⟨hgc, hb⟩⟩ := h2
      · exact ⟨hc, .inl ⟨fence, sp, sc, hf, hlt, hcl, hcta, Relation.TransGen.trans h1 ha, hb⟩⟩
      · exact ⟨hc, .inr ⟨hgc, Relation.TransGen.trans h1 hb⟩⟩
  | async i p =>
    obtain ⟨hci, w, hfin, hwf⟩ := h1
    cases g with
    | thread g => exact ⟨hci, w, hfin, Relation.TransGen.trans hwf h2⟩
    | async j q =>
      obtain ⟨hcj, ⟨_, _, _, -, -, -, -, ha, hb⟩ | ⟨-, hb⟩⟩ := h2
      · exact AsyncChain.direct ⟨hci, hcj, .inl ⟨w, hfin,
          Relation.TransGen.trans (Relation.TransGen.trans hwf ha) hb⟩⟩
      · exact AsyncChain.direct ⟨hci, hcj, .inl ⟨w, hfin, Relation.TransGen.trans hwf hb⟩⟩

/-- Wide visibility between present references, including every byte order edge between
ordinary or asynchronous writes. -/
def PresentVis (L : Launch) (X : Execution) (l : Loc) (e f : Ref) : Prop :=
  ModelCausalityChain L X l e f ∧ X.RefPresent e ∧ X.RefPresent f

/-- From an asynchronous node `a`, a visibility path ends behind an asynchronous node that `a`
sees (or `a` itself). -/
private theorem from_async {i : EvId} {p : Part} {x : Ref}
    (h : Relation.TransGen (PresentVis L X l) (.async i p) x) :
    ∃ j q, X.AsyncPresent j q ∧
      (Ref.async j q = .async i p ∨ AsyncChain L X l (i, p) (j, q)) ∧
      ModelCausalityChain L X l (.async j q) x := by
  induction h with
  | single h => exact ⟨i, p, h.2.1, .inl rfl, h.1⟩
  | @tail x y _ hxy ih =>
    obtain ⟨j, q, hp, hb, hbx⟩ := ih
    cases x with
    | thread f => exact ⟨j, q, hp, hb, hbx.trans_thread hxy.1⟩
    | async k s =>
      refine ⟨k, s, hxy.2.1, .inr ?_, hxy.1⟩
      rcases hb with he | hb
      · cases he; exact hbx
      · exact AsyncChain.trans hb hp hbx

/-- From a thread node, a visibility path is a visibility edge or passes through an
asynchronous node. -/
private theorem from_thread {n : EvId} {x : Ref}
    (h : Relation.TransGen (PresentVis L X l) (.thread n) x) :
    ModelCausalityChain L X l (.thread n) x ∨ ∃ i p,
      Relation.TransGen (PresentVis L X l) (.thread n) (.async i p) ∧
      Relation.ReflTransGen (PresentVis L X l) (.async i p) x := by
  induction h with
  | single h => exact .inl h.1
  | @tail x y hp hxy ih =>
    rcases ih with hv | ⟨i, p, h1, h2⟩
    · cases x with
      | thread f => exact .inl (hv.trans_thread hxy.1)
      | async i p => exact .inr ⟨i, p, hp, .single hxy⟩
    · exact .inr ⟨i, p, h1, h2.tail hxy⟩

/-- **Byte visibility between present references has no cycle**, given guarded
synchronization. -/
theorem modelCausality_acyclic (hv : EffectValidity L X) (hc : ObjectCoherent L X)
    (he : DepStepAcyclic L K X) (hg : SyncGuarded L K X) (hok : GuardOk L X) (n : Ref) :
    ¬ Relation.TransGen (PresentVis L X l) n n := by
  have async : ∀ i p, ¬ Relation.TransGen (PresentVis L X l) (.async i p) (.async i p) := by
    intro i p h
    obtain ⟨j, q, hp, hb, hba⟩ := from_async h
    have hp' : X.RefPresent (.async j q) := hp
    rcases hb with hb | hb
    · rw [hb] at hba hp'
      exact modelCausalityChain_asymm_guarded hv hc he hg hok hp' hba hba
    · exact modelCausalityChain_asymm_guarded (e := .async i p)
        (f := .async j q) hv hc he hg hok hp' hb hba
  intro h
  cases n with
  | async i p => exact async i p h
  | thread n =>
    rcases from_thread h with hv' | ⟨i, p, h1, h2⟩
    · exact baseCausality_irrefl hc.cause hv'
    · exact async i p (Relation.TransGen.trans_right h2 h1)

end
end PTX
