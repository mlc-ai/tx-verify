-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # A ring region's conflicts, folded by uses

A proof tool (review item 9, the kernel-free part of FA4's `Protocol/RingOrdered.lean`). The bytes
of a ring region `R` are accessed only by the ring's writers (`IsW`: copies, `cp.async` writes)
and the consumers' reads (`IsRd`: MMA operand reads), each access numbered by the ring use it
belongs to (`use`). Two conflicting accesses of a byte are then ordered (`ConflictsOrdered.of_ring`)
from four facts about uses:

* a writer before a reader of the same or a later use (`hwr`; RAW, from the full barrier:
  `NoIncObject.copy_before_read`, `SingleTmaRing.copy_read_order`);
* a reader before a writer of a later use (`hrw`; WAR, from the empty barrier:
  `read_before_copy`);
* two writers of the byte in one use are one access (`hsame`, the slot's element map);
* a writer before a writer of a later use (`hww`; through a read of the earlier use, or the
  producer's program order).

Two reads do not conflict. The kernel's part is the access classification (`hacc`, from its write
and read maps) and the four use facts. -/

namespace PTX

open AsyncCopy

variable {L : Launch} {X : Execution}

/-- Access `ref` covers byte `l`. -/
def CoversAt (X : Execution) (ref : Ref) (l : Loc) : Prop :=
  ∃ a w, X.Intent ref a w ∧ a.Covers l

/-- **The conflicts of a ring region are ordered**, from the access classification and the
order of the uses. -/
theorem ConflictsOrdered.of_ring {R : Loc → Prop} (IsW IsRd : Ref → Prop) (use : Ref → Nat)
    (hacc : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l →
      (IsW ref ∧ w = true) ∨ (IsRd ref ∧ w = false))
    (hsame : ∀ e f l, IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e = use f → e = f)
    (hww : ∀ e f l, IsW e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f)
    (hwr : ∀ e f l, IsW e → IsRd f → CoversAt X e l → CoversAt X f l → R l →
      use e ≤ use f → modelCausality L X l e f)
    (hrw : ∀ e f l, IsRd e → IsW f → CoversAt X e l → CoversAt X f l → R l →
      use e < use f → modelCausality L X l e f) :
    ConflictsOrdered L X R := by
  intro e f a b l hcon ha hb hl
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  have ce : CoversAt X e l := ⟨a, we, he, ha⟩
  have cf : CoversAt X f l := ⟨b, wf, hf, hb⟩
  rcases hacc e a we l he ha hl with ⟨hWe, -⟩ | ⟨hRe, rfl⟩ <;>
    rcases hacc f b wf l hf hb hl with ⟨hWf, -⟩ | ⟨hRf, rfl⟩
  · rcases Nat.lt_trichotomy (use e) (use f) with h | h | h
    · exact .inl (hww e f l hWe hWf ce cf hl h)
    · exact (hne (hsame e f l hWe hWf ce cf hl h)).elim
    · exact .inr (hww f e l hWf hWe cf ce hl h)
  · by_cases h : use e ≤ use f
    · exact .inl (hwr e f l hWe hRf ce cf hl h)
    · exact .inr (hrw f e l hRf hWe cf ce hl (by omega))
  · by_cases h : use f ≤ use e
    · exact .inr (hwr f e l hWf hRe cf ce hl h)
    · exact .inl (hrw e f l hRe hWf ce cf hl (by omega))
  · rcases hw with h | h <;> cases h

end PTX
