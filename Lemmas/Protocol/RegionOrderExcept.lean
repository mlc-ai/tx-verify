-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # Ordered regions with identical-value write pairs exempt

`ConflictsOrdered` with the exemption of ERR-DATA-RACE: the conflicting accesses of a byte of the
region are ordered there unless they are two writes of the same bytes with the same value
(`SameValueWrites`). An ordered whole memory leaves no race (`ConflictsOrderedExcept.no_race`);
and since such a pair has one footprint, no mixed-size conflict either
(`ConflictsOrderedExcept.no_mixed`); and the conflicts at the bytes that are read are ordered
as `ReadsOrdered` asks (`ConflictsOrderedExcept.readsOrdered`). A region ordered without exemption
is ordered with it (`ConflictsOrdered.except`), and regions combine
(`ConflictsOrderedExcept.or`). -/

namespace PTX

variable {L : Launch} {X : Execution}

/-- Conflicting accesses of a byte satisfying `R` are ordered at that byte, one way or the other,
unless they are two writes of the same bytes with the same value. -/
def ConflictsOrderedExcept (L : Launch) (X : Execution) (R : Loc → Prop) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → ¬ SameValueWrites X e f a b →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- A region ordered without exemption is ordered with it. -/
theorem ConflictsOrdered.except {R : Loc → Prop} (h : ConflictsOrdered L X R) :
    ConflictsOrderedExcept L X R :=
  fun e f a b l hc ha hb hl _ => h e f a b l hc ha hb hl

/-- Two regions ordered are ordered together. -/
theorem ConflictsOrderedExcept.or {R S : Loc → Prop} (hR : ConflictsOrderedExcept L X R)
    (hS : ConflictsOrderedExcept L X S) : ConflictsOrderedExcept L X (fun l => R l ∨ S l) :=
  fun e f a b l hc ha hb hl hE =>
    hl.elim (hR e f a b l hc ha hb · hE) (hS e f a b l hc ha hb · hE)

/-- An ordered region orders its subsets. -/
theorem ConflictsOrderedExcept.mono {R S : Loc → Prop} (hR : ConflictsOrderedExcept L X R)
    (h : ∀ l, S l → R l) : ConflictsOrderedExcept L X S :=
  fun e f a b l hc ha hb hl hE => hR e f a b l hc ha hb (h l hl) hE

/-- **No race** once every byte's conflicts are ordered, but for identical-value write pairs. -/
theorem ConflictsOrderedExcept.no_race (h : ConflictsOrderedExcept L X fun _ => True) :
    ¬ Race L X := by
  rintro ⟨e, f, a, b, l, hc, hs, ha, -, h1, h2, hE⟩
  exact (h e f a b l hc ha ((hs.covers l).mp ha) trivial hE).elim
      (fun he => h1 (.direct he)) (fun hf => h2 (.direct hf))

/-- **No mixed-size conflict** once every byte's conflicts are ordered, but for identical-value
write pairs, which have one footprint. -/
theorem ConflictsOrderedExcept.no_mixed (h : ConflictsOrderedExcept L X fun _ => True) :
    ¬ Mixed L X := by
  rintro ⟨e, f, a, b, l, hc, hs, ha, hb, h1, h2⟩
  by_cases hE : SameValueWrites X e f a b
  · exact hs hE.2.2.1
  · exact (h e f a b l hc ha hb trivial hE).elim
      (fun he => h1 (.direct he)) (fun hf => h2 (.direct hf))

/-- **The conflicts at the bytes that are read are ordered** once every byte's conflicts are
ordered, but for identical-value write pairs, which `ReadsOrdered` does not order either. -/
theorem ConflictsOrderedExcept.readsOrdered (h : ConflictsOrderedExcept L X fun _ => True) :
    ReadsOrdered L X :=
  fun _ _ _ _ _ _ e f a b hc hsv ha hb =>
    (h e f a b _ hc ha hb trivial hsv).imp .direct .direct

end PTX
