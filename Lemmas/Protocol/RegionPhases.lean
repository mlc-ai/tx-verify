-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RingRegion
public import Lemmas.Protocol.RegionOrderExcept
public import Lemmas.Protocol.StagingHandoff

@[expose] public section

/-! # A region with successive tenants

A proof tool for a shared-memory region that serves several protocols one after another (FlashMLA's
dequant tile: first the destination of the Q TMA copy and the source of `tcgen05.cp`, then a slot
of the dequant ring; its second tile: a ring slot, then the O staging buffer read by the TMA
store). The region lemmas of the library each classify *every* access of the region's bytes by one
protocol (`ConflictsOrdered.of_ring`'s `hacc`, `Staging.Ring.cover`), so they do not compose over
time: `ConflictsOrdered.or` combines byte sets, not tenants. Here:

* `ConflictsOrderedOn L X R P`: the conflicts of the accesses satisfying `P` (one tenant's) are
  ordered at the bytes of `R`; a region ordered outright is ordered for every tenant
  (`ConflictsOrdered.on`);
* `ConflictsOrdered.of_phases`: when every access of the region has a phase (`phase`), the
  conflicts within each phase are ordered (`ConflictsOrderedOn`), and an access of an earlier
  phase is visible to a conflicting access of a later one, the region is ordered; the same with
  the identical-value exemption (`ConflictsOrderedExcept.of_phases`);
* the protocols of one tenant: a ring (`ConflictsOrderedOn.of_ring`, `of_ring`'s premises for the
  tenant's accesses) and a staged buffer (`Staging.ringOn`, `Staging.Ring`'s premises with its
  cover for the tenant's accesses).

The cross-phase premise is the region's handover: typically the last uses of a tenant are
released through a barrier or a bulk-group wait that the first accesses of the next tenant
follow. -/

namespace PTX

open AsyncCopy

variable {L : Launch} {X : Execution} {R : Loc → Prop}

/-- **The conflicts of one tenant are ordered**: of the accesses satisfying `P`, conflicting ones
of a byte of `R` are ordered at that byte. -/
def ConflictsOrderedOn (L : Launch) (X : Execution) (R : Loc → Prop) (P : Ref → Prop) : Prop :=
  ∀ e f a b l, Conflict X e f a b → P e → P f → a.Covers l → b.Covers l → R l →
    modelCausality L X l e f ∨ modelCausality L X l f e

/-- `ConflictsOrderedOn` with the identical-value write pairs exempt. -/
def ConflictsOrderedExceptOn (L : Launch) (X : Execution) (R : Loc → Prop) (P : Ref → Prop) :
    Prop :=
  ∀ e f a b l, Conflict X e f a b → P e → P f → a.Covers l → b.Covers l → R l →
    ¬ SameValueWrites X e f a b → modelCausality L X l e f ∨ modelCausality L X l f e

theorem Conflict.swap {e f : Ref} {a b : Acc} (h : Conflict X e f a b) : Conflict X f e b a := by
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := h
  exact ⟨fun h => hne h.symm, wf, we, hf, he, hw.symm, hov.symm⟩

theorem SameValueWrites.swap {e f : Ref} {a b : Acc} (h : SameValueWrites X f e b a) :
    SameValueWrites X e f a b := by
  obtain ⟨hf, he, ⟨hl, hs⟩, hv⟩ := h
  exact ⟨he, hf, ⟨hl.symm, hs.symm⟩, fun bs bs' h1 h2 => (hv bs' bs h2 h1).symm⟩

/-- An ordered region is ordered for every tenant. -/
theorem ConflictsOrdered.on (h : ConflictsOrdered L X R) (P : Ref → Prop) :
    ConflictsOrderedOn L X R P :=
  fun e f a b l hc _ _ ha hb hl => h e f a b l hc ha hb hl

/-- A tenant ordered without exemption is ordered with it. -/
theorem ConflictsOrderedOn.except {P : Ref → Prop} (h : ConflictsOrderedOn L X R P) :
    ConflictsOrderedExceptOn L X R P :=
  fun e f a b l hc he hf ha hb hl _ => h e f a b l hc he hf ha hb hl

/-- **A region with successive tenants is ordered**: within each phase its conflicts are
ordered, and an access of an earlier phase is visible to a conflicting access of a later one. -/
theorem ConflictsOrdered.of_phases (phase : Ref → Nat)
    (hin : ∀ k, ConflictsOrderedOn L X R (phase · = k))
    (hcross : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l →
      phase e < phase f → modelCausality L X l e f) :
    ConflictsOrdered L X R := by
  intro e f a b l hc ha hb hl
  rcases Nat.lt_trichotomy (phase e) (phase f) with h | h | h
  · exact .inl (hcross e f a b l hc ha hb hl h)
  · exact hin (phase f) e f a b l hc h rfl ha hb hl
  · exact .inr (hcross f e b a l hc.swap hb ha hl h)

/-- **`of_phases` with the identical-value write pairs exempt.** -/
theorem ConflictsOrderedExcept.of_phases (phase : Ref → Nat)
    (hin : ∀ k, ConflictsOrderedExceptOn L X R (phase · = k))
    (hcross : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l →
      ¬ SameValueWrites X e f a b → phase e < phase f → modelCausality L X l e f) :
    ConflictsOrderedExcept L X R := by
  intro e f a b l hc ha hb hl hE
  rcases Nat.lt_trichotomy (phase e) (phase f) with h | h | h
  · exact .inl (hcross e f a b l hc ha hb hl hE h)
  · exact hin (phase f) e f a b l hc h rfl ha hb hl hE
  · exact .inr (hcross f e b a l hc.swap hb ha hl (fun h' => hE h'.swap) h)

/-- **A tenant that is a ring**: `ConflictsOrdered.of_ring` for the accesses satisfying `P`. -/
theorem ConflictsOrderedOn.of_ring {P : Ref → Prop} (IsW IsRd : Ref → Prop) (use : Ref → Nat)
    (hacc : ∀ ref a w l, P ref → X.Intent ref a w → a.Covers l → R l →
      (IsW ref ∧ w = true) ∨ (IsRd ref ∧ w = false))
    (hsame : ∀ e f l, P e → P f → IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e = use f → e = f)
    (hww : ∀ e f l, P e → P f → IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f)
    (hwr : ∀ e f l, P e → P f → IsW e → IsRd f → CoversAt X e l → CoversAt X f l → R l →
      use e ≤ use f → modelCausality L X l e f)
    (hrw : ∀ e f l, P e → P f → IsRd e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f) :
    ConflictsOrderedOn L X R P := by
  intro e f a b l hcon pe pf ha hb hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have ce : CoversAt X e l := ⟨a, we, he, ha⟩
  have cf : CoversAt X f l := ⟨b, wf, hf, hb⟩
  rcases hacc e a we l pe he ha hl with ⟨hWe, -⟩ | ⟨hRe, rfl⟩ <;>
    rcases hacc f b wf l pf hf hb hl with ⟨hWf, -⟩ | ⟨hRf, rfl⟩
  · rcases Nat.lt_trichotomy (use e) (use f) with h | h | h
    · exact .inl (hww e f l pe pf hWe hWf ce cf hl h)
    · exact (hne (hsame e f l pe pf hWe hWf ce cf hl h)).elim
    · exact .inr (hww f e l pf pe hWf hWe cf ce hl h)
  · by_cases h : use e ≤ use f
    · exact .inl (hwr e f l pe pf hWe hRf ce cf hl h)
    · exact .inr (hrw f e l pf pe hRf hWe cf ce hl (by omega))
  · by_cases h : use f ≤ use e
    · exact .inr (hwr f e l pf pe hWf hRe cf ce hl h)
    · exact .inl (hrw e f l pe pf hRe hWf ce cf hl (by omega))
  · rcases hw with h | h <;> cases h

namespace Staging

variable {gen : Nat → EvId → Prop} {rd : Nat → EvId → Nat × Nat × Nat → Prop}

/-- **A tenant that is a staged buffer**: `Staging.Ring.ordered` for the accesses satisfying `P`,
with `Ring`'s premises and its cover for those accesses. -/
theorem ringOn {P : Ref → Prop}
    (cover : ∀ e a w l, P e → X.Intent e a w → a.Covers l → R l →
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
      modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g)) :
    ConflictsOrderedOn L X R P := by
  have genRead : ∀ {j j' : Nat} {g i : EvId} {s : Nat × Nat × Nat} {a b : Acc} {we wf : Bool}
      {l : Loc}, gen j g → rd j' i s → X.Access g a we →
      X.Intent (.async i (.read (.store s.1 s.2.1 s.2.2))) b wf → (we = true ∨ wf = true) →
      a.Covers l → b.Covers l → R l →
      modelCausality L X l (.thread g) (.async i (.read (.store s.1 s.2.1 s.2.2))) ∨
        modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g) := by
    intro j j' g i s a b we wf l hg hr ha hrb hw hal hbl hl
    have hwf := Ring.read_no_write hrb
    have hwe : we = true := by
      rcases hw with h | h
      · exact h
      · rw [hwf] at h; cases h
    subst hwe
    rcases Nat.lt_or_ge j' j with h | h
    · exact .inr (release j' j i s g a l hr hg h ha hal (Ring.read_covers hrb hbl) hl)
    · exact .inl (publish j j' g i s a l hg hr h ha hal (Ring.read_covers hrb hbl) hl)
  intro e f a b l hc pe pf ha hb hl
  obtain ⟨hne, we, wf, hae, hbf, hw, -⟩ := hc
  rcases cover e a we l pe hae ha hl with ⟨j, g, rfl, hg⟩ | ⟨j, i, s, rfl, hr⟩ <;>
    rcases cover f b wf l pf hbf hb hl with ⟨j', g', rfl, hg'⟩ | ⟨j', i', s', rfl, hr'⟩
  · have hne' : g ≠ g' := fun h => hne (by rw [h])
    rcases Nat.lt_trichotomy j j' with h | rfl | h
    · exact .inl (.inl (later j j' g g' a b we wf l hg hg' h hae hbf hw ha hb hl))
    · exact (same j g g' a b we wf l hg hg' hne' hae hbf hw ha hb hl).elim
        (fun h => .inl (.inl h)) (fun h => .inr (.inl h))
    · exact .inr (.inl (later j' j g' g b a wf we l hg' hg h hbf hae hw.symm hb ha hl))
  · exact genRead hg hr' hae hbf hw ha hb hl
  · exact (genRead hg' hr hbf hae hw.symm hb ha hl).symm
  · rw [Ring.read_no_write hae, Ring.read_no_write hbf] at hw
    simp at hw

end Staging

end PTX
