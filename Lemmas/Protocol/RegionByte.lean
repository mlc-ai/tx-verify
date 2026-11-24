-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RegionOrderExcept

@[expose] public section

/-! # Regions ordered in byte causality

`ConflictsOrderedExcept` in `ByteCausality`, the order the race, mixed-size and read conditions use:
it has, besides `modelCausality`, the observed operand handoff (EXT-TC-COMMIT-OPERAND-ORDER). A
region ordered in `modelCausality` is ordered in it (`ConflictsOrdered.byte`), regions combine
(`ByteOrdered.or`), and an ordered whole memory has no race, no mixed-size conflict and ordered
reads. -/

namespace PTX

variable {L : Launch} {X : Execution}

/-- Conflicting accesses of a byte satisfying `R` are ordered at that byte, one way or the other,
unless they are two writes of the same bytes with the same value. -/
def ByteOrdered (L : Launch) (X : Execution) (R : Loc → Prop) : Prop :=
  ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → ¬ SameValueWrites X e f a b →
    ByteCausality L X l e f ∨ ByteCausality L X l f e

/-- A region ordered in `modelCausality` is ordered in `ByteCausality`. -/
theorem ConflictsOrdered.byte {R : Loc → Prop} (h : ConflictsOrdered L X R) :
    ByteOrdered L X R :=
  fun e f a b l hc ha hb hl _ => (h e f a b l hc ha hb hl).imp .direct .direct

/-- A region ordered in `modelCausality` with the exemption is ordered in `ByteCausality`. -/
theorem ConflictsOrderedExcept.byte {R : Loc → Prop} (h : ConflictsOrderedExcept L X R) :
    ByteOrdered L X R :=
  fun e f a b l hc ha hb hl hE => (h e f a b l hc ha hb hl hE).imp .direct .direct

/-- Two regions ordered are ordered together. -/
theorem ByteOrdered.or {R S : Loc → Prop} (hR : ByteOrdered L X R)
    (hS : ByteOrdered L X S) : ByteOrdered L X (fun l => R l ∨ S l) :=
  fun e f a b l hc ha hb hl hE =>
    hl.elim (hR e f a b l hc ha hb · hE) (hS e f a b l hc ha hb · hE)

/-- An ordered region orders its subsets. -/
theorem ByteOrdered.mono {R S : Loc → Prop} (hR : ByteOrdered L X R)
    (h : ∀ l, S l → R l) : ByteOrdered L X S :=
  fun e f a b l hc ha hb hl hE => hR e f a b l hc ha hb (h l hl) hE

/-- **No race** once every byte's conflicts are ordered, but for identical-value write pairs. -/
theorem ByteOrdered.no_race (h : ByteOrdered L X fun _ => True) :
    ¬ Race L X := by
  rintro ⟨e, f, a, b, l, hc, hs, ha, -, h1, h2, hE⟩
  exact (h e f a b l hc ha ((hs.covers l).mp ha) trivial hE).elim
      (fun he => h1 he) (fun hf => h2 hf)

/-- **No mixed-size conflict** once every byte's conflicts are ordered, but for identical-value
write pairs, which have one footprint. -/
theorem ByteOrdered.no_mixed (h : ByteOrdered L X fun _ => True) :
    ¬ Mixed L X := by
  rintro ⟨e, f, a, b, l, hc, hs, ha, hb, h1, h2⟩
  by_cases hE : SameValueWrites X e f a b
  · exact hs hE.2.2.1
  · exact (h e f a b l hc ha hb trivial hE).elim
      (fun he => h1 he) (fun hf => h2 hf)

/-- **The conflicts at the bytes that are read are ordered** once every byte's conflicts are
ordered, but for identical-value write pairs, which `ReadsOrdered` does not order either. -/
theorem ByteOrdered.readsOrdered (h : ByteOrdered L X fun _ => True) :
    ReadsOrdered L X :=
  fun _ _ _ _ _ _ e f a b hc hsv ha hb =>
    (h e f a b _ hc ha hb trivial hsv)

end PTX
