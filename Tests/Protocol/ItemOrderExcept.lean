-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.ItemOrderExcept

@[expose] public section

/-! # Scratch words written by a whole warp

The shape of Inkling's scratch words for `Lemmas/Kernel/Safety/ItemOrderExcept.lean`: the words
of the region are accessed by threads only, an iteration hands off to the next through a
hand-off, and within one iteration the lanes either are one thread or write the same value. Every
other region ordered outright, the execution has no race and no mixed-size conflict. -/

namespace PTX.Tests.ItemOrderExcept
open PTX PTX.Frame

variable {L : Launch} {X : Execution}

theorem scratch_no_race {R : Loc → Prop} {pair : Nat → Nat → Prop} {up uq : EvId → Nat}
    (H : Frame.Handoff L X pair up uq) (iter : EvId → Nat)
    (hcov : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l → ∃ i, ref = .thread i)
    (hlt : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → iter i < iter j → pair i.1 j.1 ∧ up i < uq j)
    (hsame : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → iter i = iter j →
      i.1 = j.1 ∨ SameValueWrites X (.thread i) (.thread j) a b)
    (hrest : ConflictsOrdered L X fun l => ¬ R l) :
    ¬ Race L X ∧ ¬ Mixed L X := by
  have h : ConflictsOrderedExcept L X fun _ => True :=
    ((ConflictsOrderedExcept.of_handoff H iter hcov hlt hsame).or hrest.except).mono
      fun l _ => Classical.em (R l)
  exact ⟨h.no_race, h.no_mixed⟩

end PTX.Tests.ItemOrderExcept
