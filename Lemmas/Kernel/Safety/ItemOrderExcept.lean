-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Protocol.RegionOrderExcept

@[expose] public section

/-! # Item orders with identical-value write pairs exempt

`Frame.ItemOrder` and `ConflictsOrdered.of_handoff` order every conflict of a region. A region
whose lanes store one value together (Inkling's scratch words: the 32 lanes of a warp write the
same word in each iteration) has conflicts that are no race (ERR-DATA-RACE exempts two writes of
the same bytes with the same value, `SameValueWrites`) and that no protocol orders. Here the
premises exempt such pairs and the conclusion is `ConflictsOrderedExcept`, which still excludes
races and mixed-size conflicts and orders the conflicts at the bytes that are read
(`Lemmas/Protocol/RegionOrderExcept.lean`):

* `ItemOrderExcept`: conflicting accesses of one item that are not identical-value writes are
  ordered, and those of an earlier item are visible to the later ones (`ItemOrderExcept.ordered`;
  an `ItemOrder` is one, `ItemOrder.except`);
* `ConflictsOrderedExcept.of_handoff`: thread accesses of different items ordered by a hand-off,
  and conflicting accesses of one item one thread's or identical-value writes. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution}

/-- **The item order of a region, identical-value write pairs exempt.** -/
structure ItemOrderExcept (L : Launch) (X : Execution) (R : Loc → Prop)
    (item : AsyncCopy.Ref → Nat) : Prop where
  /-- Conflicting accesses of one item are ordered unless they are identical-value writes. -/
  same : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → item e = item f →
    ¬ SameValueWrites X e f a b → modelCausality L X l e f ∨ modelCausality L X l f e
  /-- An access of an earlier item is visible to a conflicting access of a later item unless the
  two are identical-value writes. -/
  later : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → item e < item f →
    ¬ SameValueWrites X e f a b → modelCausality L X l e f

/-- An item order is one with the exemption. -/
theorem ItemOrder.except {R : Loc → Prop} {item : AsyncCopy.Ref → Nat}
    (h : ItemOrder L X R item) : ItemOrderExcept L X R item :=
  ⟨fun e f a b l hc ha hb hl hi _ => h.same e f a b l hc ha hb hl hi,
    fun e f a b l hc ha hb hl hi _ => h.later e f a b l hc ha hb hl hi⟩

theorem sameValueWrites_swap {e f : AsyncCopy.Ref} {a b : Acc}
    (h : SameValueWrites X f e b a) : SameValueWrites X e f a b := by
  obtain ⟨hf, he, ⟨hl, hs⟩, hv⟩ := h
  exact ⟨he, hf, ⟨hl.symm, hs.symm⟩, fun bs bs' h1 h2 => (hv bs' bs h2 h1).symm⟩

/-- **A region with an item order, identical-value pairs exempt, is ordered but for them.** -/
theorem ItemOrderExcept.ordered {R : Loc → Prop} {item : AsyncCopy.Ref → Nat}
    (h : ItemOrderExcept L X R item) : ConflictsOrderedExcept L X R := by
  intro e f a b l hc ha hb hl hE
  rcases Nat.lt_trichotomy (item e) (item f) with hlt | heq | hgt
  · exact .inl (h.later e f a b l hc ha hb hl hlt hE)
  · exact h.same e f a b l hc ha hb hl heq hE
  · exact .inr (h.later f e b a l (conflict_symm hc) hb ha hl hgt
      (fun h' => hE (sameValueWrites_swap h')))

/-- **A region of thread accesses ordered by a hand-off, identical-value pairs exempt.** Every
access of a byte of the region is a thread's (`hcov`); of two conflicting accesses of different
items, the earlier item's thread hands off to the later's (`hlt`); conflicting accesses of one
item are one thread's or identical-value writes (`heq`). -/
theorem ConflictsOrderedExcept.of_handoff {R : Loc → Prop} {pair : Nat → Nat → Prop}
    {up uq : EvId → Nat} (H : Frame.Handoff L X pair up uq) (item : EvId → Nat)
    (hcov : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l → ∃ i, ref = .thread i)
    (hlt : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → item i < item j → pair i.1 j.1 ∧ up i < uq j)
    (heq : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → item i = item j →
      i.1 = j.1 ∨ SameValueWrites X (.thread i) (.thread j) a b) :
    ConflictsOrderedExcept L X R := by
  intro e f a b l hc ha hb hl hE
  obtain ⟨hne, w, w', hi, hj, hw, hov⟩ := hc
  obtain ⟨i, rfl⟩ := hcov e a w l hi ha hl
  obtain ⟨j, rfl⟩ := hcov f b w' l hj hb hl
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hlen : ∀ {x : EvId} {c : Acc} {v : Bool}, X.Access x c v → x.2 < (X.tr x.1).length :=
    fun hx => hx.lt
  rcases Nat.lt_trichotomy (item i) (item j) with h1 | h1 | h1
  · obtain ⟨hp, hu⟩ := hlt i j a b w w' l hi hj hw ha hb hl h1
    exact .inl (.inl (H i.1 j.1 i.2 j.2 hp (hlen hj) hu))
  · rcases heq i j a b w w' l hi hj hw ha hb hl h1 with hs | hs
    · have h2 : i.2 ≠ j.2 := fun h => hij (Prod.ext hs h)
      rcases Nat.lt_or_gt_of_ne h2 with h3 | h3
      · exact .inl (.inl (.single (.inl (po_of_overlap hi hj hs h3 hov))))
      · exact .inr (.inl (.single (.inl (po_of_overlap hj hi hs.symm h3 hov.symm))))
    · exact (hE hs).elim
  · obtain ⟨hp, hu⟩ := hlt j i b a w' w l hj hi hw.symm hb ha hl h1
    exact .inr (.inl (H j.1 i.1 j.2 i.2 hp (hlen hi) hu))

end PTX.Frame
