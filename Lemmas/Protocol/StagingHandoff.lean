-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # A shared-memory staging buffer handed to the asynchronous proxy through an mbarrier

A proof tool for a buffer that generic stores fill and an asynchronous-proxy operation (a tensor
store, TMA) reads, with the handoffs made through mbarrier objects (FA4's output ring: the
correction warps stage `O / l`, the epilogue lanes store it). GEMM's output ring makes the same
handoffs through named barriers.

* **Publication** (`Publish`): a generic access `e`, a `fence.proxy.async.shared::cta` after it in
  `hb`, a release arrival of the fence's thread on an mbarrier at or after the fence, an acquire
  wait of the reader's issuing thread that observes the arrival, and the reader's issue after the
  wait. Then `e` happens before the issue (`Publish.hb`) and is visible to the reader's accesses at
  every staged byte of the fence's CTA (`Publish.modelCausality`, MEM-MODEL-CAUSALITY
  `ProxyBefore`).
* **Release** (`Release`): a tensor store's source reads, finished by a `.read` bulk-group wait
  (`cp.async.bulk.wait_group.read`, EXT-READ-WAIT-ORDER), the wait before the next generic access
  in `hb`. Then the reads are visible to that access (`Release.modelCausality`). The `hb` from the
  wait is typically a release arrival after it and an acquire wait before the access
  (`baseCausality_of_handoff`).
* **The ring** (`Ring`): the staged region's accesses are generic accesses and tensor-store source
  reads, each of a numbered item. Generic accesses of earlier items happen before those of later
  ones, the readers of an item see the generic writes of it and of earlier items, and the generic
  writes of a later item follow the readers. Then every conflict of the region is ordered
  (`Ring.ordered`, `ConflictsOrdered`), whatever the staging layout and the reuse distance: the
  premises are stated for the pairs that touch a common byte, and the kernel derives them from its
  layout. -/

namespace PTX.Staging
open AsyncCopy

section
variable {L : Launch} {X : Execution}

/-- **Synchronization through one mbarrier update.** An instruction `e` of the thread that makes
the release arrival `x` at or after it happens before every instruction `f` of the thread of an
acquire wait `w` that observes `x`, after the wait. -/
theorem baseCausality_of_handoff {e x w f : EvId} {m : Loc} {rs as : MbarScope}
    (hrel : MbarRelease X x m rs) (hobs : WaitObserves X (.thread x) w m true as)
    (hsc : ScopesMeet L rs x.1 as w.1) (hx : x.1 = e.1 ∧ e.2 ≤ x.2)
    (hw : w.1 = f.1 ∧ w.2 < f.2 ∧ f.2 < (X.tr f.1).length) : baseCausality L X e f :=
  .single (.inr (.inr (.inl ⟨x, w, m, rs, as, hrel, hobs, hsc, hw.1, hw.2.1, hw.2.2, hx.1,
    hx.2⟩)))

/-! ## Publication: generic writes before the asynchronous reader -/

/-- Generic access `e` is published to the asynchronous operation issued at `i`: a proxy fence
after `e`, a release arrival `x` of the fence's thread on `m` at or after the fence, an acquire
wait `w` of `i`'s thread observing `x`, then `i`. -/
structure Publish (L : Launch) (X : Execution) (e fence x w i : EvId) (m : Loc) : Prop where
  isFence : X.IsProxyFence fence (.async (some (.shared .cta))) none
  fence_lt : fence.1 < L.threads
  before : baseCausality L X e fence
  release : ∃ rs, MbarRelease X x m rs ∧ ∃ as, WaitObserves X (.thread x) w m true as ∧
    ScopesMeet L rs x.1 as w.1
  arrive : x.1 = fence.1 ∧ fence.2 ≤ x.2
  issue : w.1 = i.1 ∧ w.2 < i.2 ∧ i.2 < (X.tr i.1).length
  cluster : SameCluster L fence.1 i.1

namespace Publish
variable {e fence x w i : EvId} {m : Loc}

/-- The fence happens before the issue. -/
theorem fence_baseCausality (h : Publish L X e fence x w i m) : baseCausality L X fence i := by
  obtain ⟨rs, hrel, as, hobs, hsc⟩ := h.release
  exact baseCausality_of_handoff hrel hobs hsc h.arrive h.issue

/-- **The published access happens before the issue.** -/
theorem hb (h : Publish L X e fence x w i m) : baseCausality L X e i :=
  h.before.trans h.fence_baseCausality

/-- An access before the published one in `hb` is published by the same handoff. -/
theorem of_baseCausality {e' : EvId} (h : Publish L X e fence x w i m)
    (h' : PTX.baseCausality L X e' e) :
    Publish L X e' fence x w i m :=
  { h with before := h'.trans h.before }

/-- **Visibility to the reader.** At a shared byte of the fence's CTA that the reader's part `p`
covers, the published access is visible to it (MEM-MODEL-CAUSALITY, `ProxyBefore`). -/
theorem modelCausality (h : Publish L X e fence x w i m) {p : Part} {l : Loc}
    (hl : l.space = .shared)
    (hc : l.cta = fence.1 / L.block) (hcov : AsyncCovers X i p l) :
    modelCausality L X l (.thread e) (.async i p) :=
  ⟨hcov, .inl ⟨fence, _, _, h.isFence, h.fence_lt, ⟨hl, hc⟩, h.cluster, h.before,
    h.fence_baseCausality⟩⟩

end Publish

/-! ## Release: asynchronous source reads before the next generic access -/

/-- The source reads of the tensor store issued at `i` are released to generic access `f`: the
stages a `.read` bulk-group wait waits for are present (for a tensor store, its read completion),
a `.read` bulk-group wait `w` covers it, and `w` happens before `f`. -/
structure Release (L : Launch) (X : Execution) (i w f : EvId) : Prop where
  done : ∀ q ∈ GroupWaitStages X i (.bulk .read), X.AsyncPresent i q
  wait : BulkWaitsFor X .read i w
  before : baseCausality L X w f

namespace Release
variable {i w f : EvId}

/-- For a tensor store, the stages a `.read` bulk-group wait waits for are its read
completion. -/
theorem done_of_store {pc addr : Nat} {sp : TensorStore.Spec}
    (hi : X.get i = some ⟨pc, .tensorStore addr sp⟩) (hd : X.AsyncPresent i .readsDone) :
    ∀ q ∈ GroupWaitStages X i (.bulk .read), X.AsyncPresent i q := by
  intro q hq
  simp only [GroupWaitStages, hi, Option.map_some, List.mem_singleton] at hq
  exact hq ▸ hd

/-- An access after the released one in `hb` is released by the same wait. -/
theorem of_baseCausality {f' : EvId} (h : Release L X i w f)
    (h' : baseCausality L X f f') : Release L X i w f' :=
  { h with before := h.before.trans h' }

/-- **Visibility of the source reads** to the released access at a byte they cover
(EXT-READ-WAIT-ORDER: no proxy fence). -/
theorem modelCausality (h : Release L X i w f) {x y k : Nat} {l : Loc}
    (hcov : AsyncCovers X i (.read (.store x y k)) l) :
    modelCausality L X l (.async i (.read (.store x y k))) (.thread f) :=
  ⟨hcov, w, .inl ⟨.bulk .read, rfl, h.wait, h.done⟩, .inl h.before⟩

end Release

/-! ## The ring of a staged region -/

/-- The accesses of the region `R`: generic accesses `gen j e` and tensor-store source reads
`rd j i (x, y, k)` of numbered items `j`, ordered item by item. Each ordering premise is stated
for two accesses that touch a common byte of the region with one of them writing. -/
structure Ring (L : Launch) (X : Execution) (R : Loc → Prop) (gen : Nat → EvId → Prop)
    (rd : Nat → EvId → Nat × Nat × Nat → Prop) : Prop where
  /-- Every access of a byte of the region is a generic access or a source read of an item. -/
  cover : ∀ e a w l, X.Intent e a w → a.Covers l → R l →
    (∃ j g, e = .thread g ∧ gen j g) ∨
      ∃ j i s, e = .async i (.read (.store s.1 s.2.1 s.2.2)) ∧ rd j i s
  /-- Conflicting generic accesses of one item are ordered. -/
  same : ∀ j g g' a a' w w' l, gen j g → gen j g' → g ≠ g' → X.Access g a w →
    X.Access g' a' w' → (w = true ∨ w' = true) → a.Covers l → a'.Covers l → R l →
    baseCausality L X g g' ∨ baseCausality L X g' g
  /-- Generic accesses of an earlier item happen before conflicting ones of a later item. -/
  later : ∀ j j' g g' a a' w w' l, gen j g → gen j' g' → j < j' → X.Access g a w →
    X.Access g' a' w' → (w = true ∨ w' = true) → a.Covers l → a'.Covers l → R l →
    baseCausality L X g g'
  /-- A generic write of an item is visible to the source reads of the same or a later item. -/
  publish : ∀ j j' g i s a l, gen j g → rd j' i s → j ≤ j' → X.Access g a true → a.Covers l →
    AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l → R l →
    modelCausality L X l (.thread g) (.async i (.read (.store s.1 s.2.1 s.2.2)))
  /-- The source reads of an item are visible to a generic write of a later item. -/
  release : ∀ j j' i s g a l, rd j i s → gen j' g → j < j' → X.Access g a true → a.Covers l →
    AsyncCovers X i (.read (.store s.1 s.2.1 s.2.2)) l → R l →
    modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g)

namespace Ring
variable {R : Loc → Prop} {gen : Nat → EvId → Prop} {rd : Nat → EvId → Nat × Nat × Nat → Prop}

/-- A source read does not write. -/
theorem read_no_write {i : EvId} {x y k : Nat} {a : Acc} {w : Bool}
    (h : X.Intent (.async i (.read (.store x y k))) a w) : w = false := h.1

/-- A source read's footprint at a covered byte. -/
theorem read_covers {i : EvId} {x y k : Nat} {a : Acc} {w : Bool} {l : Loc}
    (h : X.Intent (.async i (.read (.store x y k))) a w) (hl : a.Covers l) :
    AsyncCovers X i (.read (.store x y k)) l :=
  ⟨a, w, h, hl⟩

/-- A generic access with a source read: ordered one way by the item numbers. -/
theorem gen_read (hR : Ring L X R gen rd) {j j' : Nat} {g i : EvId} {s : Nat × Nat × Nat}
    {a b : Acc} {we wf : Bool} {l : Loc} (hg : gen j g) (hr : rd j' i s)
    (ha : X.Access g a we) (hrb : X.Intent (.async i (.read (.store s.1 s.2.1 s.2.2))) b wf)
    (hw : we = true ∨ wf = true) (hal : a.Covers l) (hbl : b.Covers l) (hl : R l) :
    modelCausality L X l (.thread g) (.async i (.read (.store s.1 s.2.1 s.2.2))) ∨
      modelCausality L X l (.async i (.read (.store s.1 s.2.1 s.2.2))) (.thread g) := by
  have hwf := read_no_write hrb
  have hwe : we = true := by
    rcases hw with h | h
    · exact h
    · rw [hwf] at h; cases h
  subst hwe
  rcases Nat.lt_or_ge j' j with h | h
  · exact .inr (hR.release j' j i s g a l hr hg h ha hal (read_covers hrb hbl) hl)
  · exact .inl (hR.publish j j' g i s a l hg hr h ha hal (read_covers hrb hbl) hl)

/-- **Every conflict of the staged region is ordered.** -/
theorem ordered (hR : Ring L X R gen rd) : ConflictsOrdered L X R := by
  intro e f a b l hc ha hb hl
  obtain ⟨hne, we, wf, hae, hbf, hw, -⟩ := hc
  rcases hR.cover e a we l hae ha hl with ⟨j, g, rfl, hg⟩ | ⟨j, i, s, rfl, hr⟩ <;>
    rcases hR.cover f b wf l hbf hb hl with ⟨j', g', rfl, hg'⟩ | ⟨j', i', s', rfl, hr'⟩
  · have hne' : g ≠ g' := fun h => hne (by rw [h])
    rcases Nat.lt_trichotomy j j' with h | rfl | h
    · exact .inl (.inl (hR.later j j' g g' a b we wf l hg hg' h hae hbf hw ha hb hl))
    · exact (hR.same j g g' a b we wf l hg hg' hne' hae hbf hw ha hb hl).elim
        (fun h => .inl (.inl h)) (fun h => .inr (.inl h))
    · exact .inr (.inl (hR.later j' j g' g b a wf we l hg' hg h hbf hae hw.symm hb ha hl))
  · exact hR.gen_read hg hr' hae hbf hw ha hb hl
  · exact (hR.gen_read hg' hr hbf hae hw.symm hb ha hl).symm
  · rw [read_no_write hae, read_no_write hbf] at hw
    simp at hw

end Ring

end

end PTX.Staging
