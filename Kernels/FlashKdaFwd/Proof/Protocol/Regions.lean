-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Init
public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # Who touches which bytes when: the regions of shared memory

A data race or a mixed-size conflict
(two classes of `Unsafe`) is excluded once any two conflicting accesses of a common byte are
ordered there (`ConflictsOrdered`, `Lemmas/Protocol/RegionOrder.lean`). The kernel proves this
region by region.

* **`state_acc`** (`InStateAcc`): only threads touch it. Before the fourth `bar.sync 0` every
  thread writes its own elements (the conversion of the initial state); after the sixth, each
  byte is read and written by one compute thread only (its own rows of the bf16 state). The
  library lemma is `Frame.ConflictsOrdered.of_handoff` with the hand-off of the CTA barrier and
  the item "number of `bar.sync 0` before the access" (`StateAccFacts.ordered`).
* **The union region** (`InUnion`): threads and the copy engine touch it. The library lemma is
  `Frame.ItemOrder.ordered`: number every access by an *epoch* so that conflicting accesses of
  one epoch are ordered and an access of an earlier epoch is visible to a conflicting access of
  a later one. The epochs and the lemma that gives each pair are tabulated in the plan; the
  pairwise lemmas are those of `Fences.lean`, `StoreRing.lean`, `LoadRing.lean` and
  `StateBar.lean`. Here the order is a premise (`unionOrdered`).
* **Everything else** (global memory, the 88 bytes of the mbarrier objects) is `Rest`.

`noRace_noMixed` puts the regions together. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat}

/-- An event that is no `bar.sync 0` does not change the count. -/
theorem bar0UpTo_of_not_bar {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hn : Execution.isBarId 0 e = false) : bar0UpTo X (g, k) = bar0Before X (g, k) := by
  have hg : (X.tr g)[k]? = some e := he
  simp only [bar0UpTo, bar0Before]
  rw [List.take_add_one, hg, Option.toList_some, List.countP_append]
  simp [hn]

/-- A memory access is no barrier event. -/
theorem bar0UpTo_of_access {g k : Nat} {a : Acc} {w : Bool} (h : X.Access (g, k) a w) :
    bar0UpTo X (g, k) = bar0Before X (g, k) := by
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩ <;>
    exact bar0UpTo_of_not_bar he rfl

/-- **Thread-layer facts about the accesses of `state_acc`.** -/
structure StateAccFacts (L : Launch) (X : Execution) : Prop where
  /-- Only threads access `state_acc`: no load, store or other asynchronous operation. -/
  thread_only : ∀ {ref : Ref} {a : Acc} {w : Bool} {l : Loc} {c : Nat}, X.Intent ref a w →
    a.Covers l → InStateAcc L c l → ∃ i, ref = .thread i
  /-- An access of `state_acc` is a thread's of the same CTA, in the conversion loop (three
  `bar.sync 0` before it) or in the tile loop (six). -/
  phase : ∀ {g i : Nat} {a : Acc} {w : Bool} {l : Loc} {c : Nat}, X.Access (g, i) a w →
    a.Covers l → InStateAcc L c l →
      g < L.threads ∧ c = g / L.block ∧
      (bar0Before X (g, i) = 3 ∨ bar0Before X (g, i) = 6)
  /-- Within one of the two phases a byte of `state_acc` belongs to one thread. -/
  owner : ∀ {g i h j : Nat} {a b : Acc} {w w' : Bool} {l : Loc} {c : Nat},
    X.Access (g, i) a w → X.Access (h, j) b w' → (w = true ∨ w' = true) → a.Covers l →
    b.Covers l → InStateAcc L c l → bar0Before X (g, i) = bar0Before X (h, j) → g = h

/-- **Every conflict on `state_acc` is ordered.** -/
theorem StateAccFacts.ordered (hA : StateAccFacts L X) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (c : Nat) :
    ConflictsOrdered L X (InStateAcc L c) :=
  ConflictsOrdered.of_handoff (hB.handoff0 hX hb) (bar0Before X)
    (fun _ _ _ _ hi ha hl => hA.thread_only hi ha hl)
    (fun i j _ _ _ _ _ hi hj _ ha hb' hl hlt => by
      obtain ⟨hg, hc, -⟩ := hA.phase (g := i.1) (i := i.2) hi ha hl
      obtain ⟨hh, hc', -⟩ := hA.phase (g := j.1) (i := j.2) hj hb' hl
      exact ⟨⟨hg, hh, hc.symm.trans hc'⟩,
        by rw [bar0UpTo_of_access (g := i.1) (k := i.2) hi]; exact hlt⟩)
    (fun i j _ _ _ _ _ hi hj hw ha hb' hl heq =>
      hA.owner (g := i.1) (i := i.2) (h := j.1) (j := j.2) hi hj hw ha hb' hl heq)

/-- **Every conflict on the union region is ordered**, from an epoch numbering of its accesses
(`Frame.ItemOrder`). -/
theorem unionOrdered {c : Nat} {epoch : Ref → Nat}
    (h : ItemOrder L X (InUnion L c) epoch) : ConflictsOrdered L X (InUnion L c) :=
  h.ordered

/-- **No data race and no mixed-size conflict**, from the three kinds of region. -/
theorem noRace_noMixed {Rest : Loc → Prop}
    (hacc : ∀ c, ConflictsOrdered L X (InStateAcc L c))
    (hun : ∀ c, ∃ epoch : Ref → Nat, ItemOrder L X (InUnion L c) epoch)
    (hrest : ConflictsOrdered L X Rest)
    (hcover : ∀ l, (∃ c, InStateAcc L c l) ∨ (∃ c, InUnion L c l) ∨ Rest l) :
    ¬ Race L X ∧ ¬ Mixed L X := by
  have hall : ConflictsOrdered L X (fun _ => True) := by
    intro e f a b l hc ha hb _
    rcases hcover l with ⟨c, hl⟩ | ⟨c, hl⟩ | hl
    · exact hacc c e f a b l hc ha hb hl
    · obtain ⟨ep, ho⟩ := hun c
      exact ho.ordered e f a b l hc ha hb hl
    · exact hrest e f a b l hc ha hb hl
  exact ⟨hall.no_race, hall.no_mixed⟩

end PTX.Kernels.FlashKdaFwd.Protocol
