-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.BrSegs

@[expose] public section

/-! # The bridge's exit: the epilogue's entry facts

The facts at the end of the bridge's first part (pc 2565, the epilogue's poll of `o_final`) are
the registers live there valued by `valueB i`. They give the epilogue's
`entryFacts (prm i) i.skip`: each register's value is the epilogue table's, by evaluation
(`valueB_eq_valueOf`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The epilogue's entry state from the bridge's state: the poll, with `%p173` the flag. -/
abbrev dE (i : In) : D := D.entry (prm i) i.skip

/-! ### The values are the epilogue's -/

theorem live2565_keys : ∀ r ∈ Flow.live 2565, r = 3 ∨ r = 173 ∨ r = 175 ∨ r = 462 ∨ r = 463 ∨
    r = 464 ∨ r = 478 ∨ r = 491 ∨ r = 496 ∨ r = 497 ∨ r = 524 ∨ r = 533 ∨ r = 610 ∨ r = 624 ∨
    r = 1760 ∨ r = 1915 ∨ r = 1956 ∨ r = 2023 ∨ r = 2024 := by
  decide +kernel

/-- **On the registers live at the epilogue's poll, the bridge's values are the epilogue's.** -/
theorem valueB_eq_valueOf (i : In) : ∀ r ∈ Flow.live 2565, valueB i r = valueOf (dE i) r := by
  intro r hr
  rcases live2565_keys r hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ### The facts -/

theorem entry_of_facts {R : Nat → Option Value} (i : In) (h : Holds R (bfacts 2565 i)) :
    Holds R (entryFacts (prm i) i.skip) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  have h1 := holds_mem h (Flow.mem_factsFrom (val := valueB i) hr)
  rw [h1, valueB_eq_valueOf i r hr]

end
end PTX.Kernels.InklingRelDecode.Proof.Br
