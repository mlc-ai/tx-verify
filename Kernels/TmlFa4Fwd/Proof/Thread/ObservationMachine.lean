-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Prologue
public import Lemmas.Execution.ShapeExecution
public import Lemmas.Flow.Machine
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

noncomputable section

/-- The role state records the observations of an actual prefix at a stopping point. -/
def observationMachine {σ : Type} (l : Launch) (g : Nat) (init : σ)
    (advance : σ → Event → σ) : Machine kernel Assumptions.all l g where
  St := σ
  init := init
  Good s t :=
    ∃ es, TraceReach kernel Assumptions.all l g {} es t ∧
      es.foldl advance init = s ∧ Stops kernel Assumptions.all l g t
  tmpl _ t :=
    match out kernel Assumptions.all l g t with
    | .ev tm => tm
    | .tau _ => .ub .noRule
  next s e := some (advance s e)

theorem observationSound {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {σ : Type} (init : σ) (advance : σ → Event → σ) :
    (observationMachine l g init advance).Sound := by
  let M := observationMachine l g init advance
  have hout {s t} (ht : M.Good s t) : out kernel Assumptions.all l g t = .ev (M.tmpl s t) := by
    obtain ⟨_, _, _, tm, ht⟩ := ht
    simp [M, observationMachine, ht]
  refine ⟨?_, hout, ?_⟩
  · obtain ⟨t, hn, _⟩ := Prologue.firstBroadcastWith (A := Assumptions.all) hp g
    exact ⟨t, hn.steps, [], TraceReach.of_local hn.steps, rfl, _, hn.stop⟩
  · intro s t e u ht hf
    have he : EStep kernel Assumptions.all l g t e (some u) := ⟨_, hout ht, hf⟩
    obtain ⟨es, hp, hs, _⟩ := ht
    refine .inl ⟨advance s e, rfl, ?_⟩
    intro v hv hStop
    refine ⟨es ++ [e], hp.append (.event he (TraceReach.of_local hv)), ?_, hStop⟩
    rw [List.foldl_append, hs]
    rfl

/-- Every prefix state is the fold of its role's event observations. -/
@[simp] theorem observationAfter {σ : Type} (l : Launch) (g : Nat) (init s : σ)
    (advance : σ → Event → σ) (es : List Event) :
    (observationMachine l g init advance).after s es = some (es.foldl advance s) := by
  induction es generalizing s with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- A reached event is certified at the role state summarizing its prior events. -/
theorem observationFired {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {e : Event} (he : X.get i = some e)
    {σ : Type} (init : σ) (advance : σ → Event → σ) :
    ∃ o, (observationMachine l i.1 init advance).Fired
      (((X.tr i.1).take i.2).foldl advance init) e o := by
  have hg := PTX.Proof.event_thread_lt hX he
  have ht := (observationSound hp i.1 init advance).produces (hX.thr i.1 hg)
  exact ht.fired_at he (observationAfter l i.1 init init advance _)

/-- The state before the indicated event, or the current state at the end of the prefix. -/
def stateAt {l : Launch} {g : Nat} (M : Machine kernel Assumptions.all l g)
    (X : Execution) (index : Nat) : Option M.St :=
  M.after M.init ((X.tr g).take index)

/-- An actual event of a thread and its abstract transition. -/
def Transition {l : Launch} {g : Nat} (M : Machine kernel Assumptions.all l g)
    (X : Execution) (index : Nat) (kind : Kind) (before after : M.St) : Prop :=
  ∃ e, X.get (g, index) = some e ∧ e.kind = kind ∧
    stateAt M X index = some before ∧ M.next before e = some after

/-- A transition at an actual event certifies the next prefix state. -/
theorem Transition.stateAfter {l : Launch} {g : Nat}
    {M : Machine kernel Assumptions.all l g} {X : Execution} {index : Nat}
    {kind : Kind} {before after : M.St} (h : Transition M X index kind before after) :
    stateAt M X (index + 1) = some after := by
  obtain ⟨e, he, _, hState, hNext⟩ := h
  have he' : (X.tr g)[index]? = some e := he
  have hi := (List.getElem?_eq_some_iff.mp he').1
  have hTake : (X.tr g).take (index + 1) = (X.tr g).take index ++ [e] := by
    rw [List.take_succ_eq_append_getElem hi, (List.getElem?_eq_some_iff.mp he').2]
  unfold stateAt at hState ⊢
  rw [hTake, M.after_snoc, hState]
  exact hNext

end
end PTX.Kernels.TmlFa4Fwd.Thread
