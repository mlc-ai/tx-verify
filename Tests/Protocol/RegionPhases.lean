-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RegionPhases

@[expose] public section

/-! # FlashMLA's two dequant tiles as regions with successive tenants

The shapes of `Lemmas/Protocol/RegionPhases.lean` at FlashMLA's tiles (the premises are the
kernel's): the first tile is the Q TMA destination read by `tcgen05.cp` (phase 0, one ring use),
then a dequant ring slot (phase 1, a ring of generic writers and MMA readers); the second tile is
a ring slot (phase 0), then the O staging buffer read by the TMA store (phase 1, `Staging`). -/

namespace PTX.Tests.RegionPhases
open PTX AsyncCopy

variable {L : Launch} {X : Execution} {R : Loc → Prop}

/-- The first tile: a single-use ring, then a ring. -/
theorem tile0 (phase : Ref → Nat) (IsW IsRd : Ref → Prop) (use : Ref → Nat)
    (hacc : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l →
      (IsW ref ∧ w = true) ∨ (IsRd ref ∧ w = false))
    (hsame : ∀ e f l, phase e = phase f → IsW e → IsW f → CoversAt X e l → CoversAt X f l →
      R l → use e = use f → e = f)
    (hww : ∀ e f l, phase e = phase f → IsW e → IsW f → CoversAt X e l → CoversAt X f l →
      R l → use e < use f → modelCausality L X l e f)
    (hwr : ∀ e f l, phase e = phase f → IsW e → IsRd f → CoversAt X e l → CoversAt X f l →
      R l → use e ≤ use f → modelCausality L X l e f)
    (hrw : ∀ e f l, phase e = phase f → IsRd e → IsW f → CoversAt X e l → CoversAt X f l →
      R l → use e < use f → modelCausality L X l e f)
    (hcross : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l →
      phase e < phase f → modelCausality L X l e f) :
    ConflictsOrdered L X R := by
  refine ConflictsOrdered.of_phases phase (fun k => ?_) hcross
  refine ConflictsOrderedOn.of_ring IsW IsRd use (fun ref a w l _ => hacc ref a w l)
    (fun e f l pe pf => hsame e f l (pe.trans pf.symm))
    (fun e f l pe pf => hww e f l (pe.trans pf.symm))
    (fun e f l pe pf => hwr e f l (pe.trans pf.symm))
    (fun e f l pe pf => hrw e f l (pe.trans pf.symm))

/-- The second tile: a ring tenant ordered on its own, then a staged buffer. -/
theorem tile1 (phase : Ref → Nat) {gen : Nat → EvId → Prop}
    {rd : Nat → EvId → Nat × Nat × Nat → Prop}
    (hring : ConflictsOrderedOn L X R (phase · = 0))
    (hph : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l → phase ref ≤ 1)
    (cover : ∀ e a w l, phase e = 1 → X.Intent e a w → a.Covers l → R l →
      (∃ j g, e = .thread g ∧ gen j g) ∨
        ∃ j i s, e = .async i (.read (.store s.1 s.2.1 s.2.2)) ∧ rd j i s)
    (same : ∀ j g g' a a' w w' l, gen j g → gen j g' → g ≠ g' → X.Access g a w →
      X.Access g' a' w' → (w = true ∨ w' = true) → a.Covers l → a'.Covers l → R l →
      baseCausality L X g g' ∨ baseCausality L X g' g)
    (later : ∀ j j' g g' a a' w w' l, gen j g → gen j' g' → j < j' → X.Access g a w →
      X.Access g' a' w' → (w = true ∨ w' = true) → a.Covers l → a'.Covers l → R l →
      baseCausality L X g g')
    (publish : ∀ j j' g i s a l, gen j g → rd j' i s → j ≤ j' → X.Access g a true →
      a.Covers l → AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l → R l →
      modelCausality L X l (.thread g) (.async i (.read (.store s.1 s.2.1 s.2.2))))
    (release : ∀ j j' i s g a l, rd j i s → gen j' g → j < j' → X.Access g a true →
      a.Covers l → AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l → R l →
      modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g))
    (hcross : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l →
      phase e < phase f → modelCausality L X l e f) :
    ConflictsOrdered L X R := by
  refine ConflictsOrdered.of_phases phase (fun k => ?_) hcross
  rcases Nat.lt_or_ge k 2 with hk | hk
  · rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact hring
    · exact Staging.ringOn cover same later publish release
  · intro e f a b l hc pe _ ha _ hl
    obtain ⟨-, we, -, he, -⟩ := hc
    have := hph e a we l he ha hl
    omega

end PTX.Tests.RegionPhases
