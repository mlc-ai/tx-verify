-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! Causality edges between thread instructions: an instruction's issue-to-return stage step and
base causality from a return to a later issue. -/

namespace PTX

section
variable {L : Launch} {X : Execution}

/-- A base causality edge from the return of `i` to the issue of `j`. -/
theorem stageCausality.of_baseCausality {i j : EvId} (h : baseCausality L X i j) :
    stageCausality L X (.thread i, true) (.thread j, false) :=
  Or.inr (Or.inl ⟨rfl, rfl, i, j, rfl, rfl, h⟩)

/-- The issue-to-return step of a present instruction. -/
theorem stageCausality.of_present {e : EvId} {ev : Event} (h : X.get e = some ev) :
    stageCausality L X (.thread e, false) (.thread e, true) :=
  Or.inl (Or.inl ⟨rfl, rfl, rfl, ⟨ev, h⟩⟩)

/-- Causality from the issue of `i` to the issue of a program-order successor. -/
theorem stageCausality.issue_po {i j : EvId} {ev : Event} (hi : X.get i = some ev) (h : po X i j) :
    Relation.TransGen (stageCausality L X) (.thread i, false) (.thread j, false) :=
  .head (stageCausality.of_present hi)
      (.single (stageCausality.of_baseCausality (.single (.inl h))))

end

end PTX
