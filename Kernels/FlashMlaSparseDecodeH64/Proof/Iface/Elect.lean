-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec

@[expose] public section

/-! # One elected lane per CTA: the common form

An election fact of a single-lane role (MMA: `Iface/Elect/Mma.lean`; TMA:
`Iface/Elect/Tma.lean`) says that two lanes of one CTA with events where `On` holds (the role's
pcs after its election) are one lane (`OneLane`). Then every such event is of the CTA's lane
`laneOn` (`laneOn_eq`). The events are not undefined behaviour: a lane that lost the election
may fault on its way to the idle code at a pc of the role (the crossing's local instructions),
and its machine does not see that pc. These are election facts, not classification rows: they
are not checked against the code, and each file states which exports of its producer imply it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- Two lanes of one CTA with events where `On` holds, not undefined behaviour, are one lane. -/
def OneLane (L : Launch) (X : Execution) (On : Nat → Nat → Prop) : Prop :=
  ∀ {g g' k k' : Nat} {e e' : Event}, X.get (g, k) = some e → X.get (g', k') = some e' →
    (∀ f, e.kind ≠ .ub f) → (∀ f, e'.kind ≠ .ub f) →
    On g e.pc → On g' e'.pc → g / L.block = g' / L.block → g = g'

open Classical in
/-- The lane of CTA `c` with an event where `On` holds, not undefined behaviour (`0` when none
has). -/
def laneOn (L : Launch) (X : Execution) (On : Nat → Nat → Prop) (c : Nat) : Nat :=
  if h : ∃ y k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ On y e.pc ∧ y / L.block = c
  then Classical.choose h
  else 0

/-- **A lane with an event where `On` holds is its CTA's `laneOn`.** -/
theorem laneOn_eq {On : Nat → Nat → Prop} (hO : OneLane L X On) {y k : Nat} {e : Event}
    (he : X.get (y, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (hat : On y e.pc) :
    y = laneOn L X On (y / L.block) := by
  have hex : ∃ y' k e, X.get (y', k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ On y' e.pc ∧
      y' / L.block = y / L.block :=
    ⟨y, k, e, he, hu, hat, rfl⟩
  unfold laneOn
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨k', e', he', hu', hat', hc⟩ := Classical.choose_spec hex
  exact hO he he' hu hu' hat hat' hc.symm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
