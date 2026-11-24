-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Fragment

@[expose] public section

/-! # Lifting thread facts between kinds of executions

A proof tool. Thread, protocol and value facts are stated once, for an arbitrary consistent
execution. These lemmas connect the other notions to that one:

* a maximal execution is consistent (`maximal_consistent`), so every such fact applies to it;
* in a complete execution every launched thread that was not canceled ends with an exit
  (`Complete.exit_last`), fired from a followed state of its machine (`exit_state`) whose shape
  table says so (`exit_ev`, for fragments).

An execution with a poll appended is consistent by `Frame.poll_consistent`
(`Lemmas/Step/Released.lean`). -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A maximal execution is consistent. -/
theorem maximal_consistent (hM : Maximal L K A mem0 X) : Consistent L K A mem0 X := hM.1

/-- **In a complete execution a launched thread that was not canceled ends with an exit.** -/
theorem Complete.exit_last (hc : Complete L X) (hg : g < L.threads) (hcl : ¬ ClcCanceled L X g) :
    ∃ k pc, k + 1 = (X.tr g).length ∧ X.get (g, k) = some ⟨pc, .exit⟩ := by
  rcases hc.1 g hg with h | ⟨pc, hl⟩
  · exact absurd h hcl
  · have hne : X.tr g ≠ [] := fun h => by rw [h] at hl; cases hl
    have hpos : 0 < (X.tr g).length := List.length_pos_iff.mpr hne
    refine ⟨(X.tr g).length - 1, pc, by omega, ?_⟩
    change (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?, hl]

/-- **The exit of a complete execution's thread fires from a followed state.** -/
theorem exit_state {C : (g : Nat) → Code K A L g} (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (ht : Tracked C X) (hc : Complete L X) (hg : g < L.threads)
    (hcl : ¬ ClcCanceled L X g) :
    ∃ k pc d, k + 1 = (X.tr g).length ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      stateAt C X g k = some (some d) := by
  obtain ⟨k, pc, hk, he⟩ := Complete.exit_last hc hg hcl
  obtain ⟨d, hd⟩ := event_state hC hX ht he fun pc' f h => by cases h
  exact ⟨k, pc, d, hk, he, hd⟩

/-- For fragments: the state the exit fires from has the exit in its shape table. -/
theorem exit_ev {F : (g : Nat) → Fragment K A L g} (hC : ∀ g < L.threads, (F g).code.Sound)
    (hok : ∀ g < L.threads, (F g).Ok) (hX : Consistent L K A mem0 X) (ht : Tracked (codes F) X)
    (hc : Complete L X) (hg : g < L.threads) (hcl : ¬ ClcCanceled L X g) :
    ∃ k pc d, k + 1 = (X.tr g).length ∧ X.get (g, k) = some ⟨pc, .exit⟩ ∧
      stateAt (codes F) X g k = some (some d) ∧ (F g).Ev d ⟨pc, .exit⟩ := by
  obtain ⟨k, pc, d, hk, he, hd⟩ := exit_state (C := codes F) hC hX ht hc hg hcl
  exact ⟨k, pc, d, hk, he, hd, (fired_ev hC hok hX he hd).1⟩

end

end PTX.Frame
