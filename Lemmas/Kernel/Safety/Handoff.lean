-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitHandoff
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Protocol.NamedBarMember
public import Lemmas.Protocol.RegionOrder

@[expose] public section

/-! # The hand-off order between a region's writers and readers

A proof tool, generic over the kernel. A synchronization a kernel declares between two roles
(an mbarrier unit hand-off, a named or CTA barrier) orders events by their *uses*: counts of the
threads' events of the synchronization before them, which a role's ghost ledger keeps as fields
of its states (`Code.counted`, `Frame.count_eq`). The order is stated once in that form
(`Handoff`): for a pair of threads `g ⇝ h` of the declaration, an event of `g` whose producer use
is below the consumer use of an event of `h` happens before it (base causality).

* **Instances.** An mbarrier unit hand-off (`MbarRing.UnitHandoff`) is one, with the producer's
  arrivals on the object as its use and the consumer's successful polls less the offset as the
  consumer's (`Handoff.of_unit`). A named barrier is one from its participants, which arrive by
  either form, to its participants that arrive by `bar.sync`, in one CTA, with the barrier's
  arrivals up to and including the event as the producer's use and those before the event as the
  consumer's (`Handoff.of_bar`; a CTA barrier is the named barrier `0` of every warp). Hand-offs
  compose through an event of the middle thread (`Handoff.comp`).
* **Regions by items** (`ItemOrder`): the accesses of a region are numbered by items (a function
  of the access, in practice of its issuing event's counts); conflicting accesses of one item are
  ordered one way or the other, and those of an earlier item are visible to those of a later one.
  Then every conflict of the region is ordered (`ItemOrder.ordered`, `ConflictsOrdered`), whatever
  kind of access (thread, copy, tensor load or store, MMA read) the region has.
* **Regions of thread accesses** (`ConflictsOrdered.of_handoff`): when every access of the region
  is a thread's, the items of conflicting accesses of different threads are ordered by a hand-off
  (`up` of the earlier below `uq` of the later), and conflicting accesses of one item are one
  thread's, every conflict is ordered: across items by the hand-off, within one thread by
  program order (`po_of_overlap`).

ERR-DATA-RACE and ERR-MIXED-SIZE then follow from the regions covering every byte
(`ConflictsOrdered.or`, `ConflictsOrdered.no_race`, `ConflictsOrdered.no_mixed`). Which accesses
reach a region, and the items of each, a kernel reads off its role table
(`RoleTable.intent_at` in `Lemmas/Kernel/Safety/Classes.lean`). -/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution}

/-- **A hand-off order**: for a pair `g ⇝ h` of `pair`, an event of `g` whose producer use `up` is
below the consumer use `uq` of an event of `h` happens before that event. -/
def Handoff (L : Launch) (X : Execution) (pair : Nat → Nat → Prop) (up uq : EvId → Nat) :
    Prop :=
  ∀ g h e f, pair g h → f < (X.tr h).length → up (g, e) < uq (h, f) →
    baseCausality L X (g, e) (h, f)

namespace Handoff

variable {pair : Nat → Nat → Prop} {up uq : EvId → Nat}

/-- A hand-off holds for fewer pairs. -/
theorem mono (H : Handoff L X pair up uq) {pair' : Nat → Nat → Prop}
    (hp : ∀ g h, pair' g h → pair g h) : Handoff L X pair' up uq :=
  fun g h e f hgh hf hlt => H g h e f (hp g h hgh) hf hlt

/-- **Two hand-offs compose** through an event of the middle thread: after the first's consumer
use and before the second's producer use. -/
theorem comp (H1 : Handoff L X pair up uq) {pair' : Nat → Nat → Prop} {up' uq' : EvId → Nat}
    (H2 : Handoff L X pair' up' uq') {g h k e j f : Nat} (h1 : pair g h) (h2 : pair' h k)
    (hj : j < (X.tr h).length) (hf : f < (X.tr k).length) (hv : up (g, e) < uq (h, j))
    (hu : up' (h, j) < uq' (k, f)) : baseCausality L X (g, e) (k, f) :=
  Relation.TransGen.trans (H1 g h e j h1 hj hv) (H2 h k j f h2 hf hu)

/-- **An mbarrier unit hand-off** is a hand-off from its producers to its consumers: the
producer's use is its arrivals on the object before the event, the consumer's its successful
polls of the object before the event less the offset. -/
theorem of_unit {m : Loc} {prod cons : Nat → Prop} {δ : Nat}
    (hU : MbarRing.UnitHandoff L X m prod cons δ) :
    Handoff L X (fun g h => prod g ∧ cons h) (fun i => arrivals m ((X.tr i.1).take i.2))
      (fun i => okPolls m ((X.tr i.1).take i.2) - δ) := by
  rintro g h e f ⟨hg, hh⟩ hf hlt
  exact hU.baseCausality_of_counts (q := arrivals m ((X.tr g).take e)) hh hg le_rfl
    (by simp only at hlt; omega) hf

/-- The events of a thread satisfying `P` up to and including position `e`. -/
theorem countP_take_succ_ge {P : Event → Bool} {es : List Event} {i e : Nat} {ev : Event}
    (hev : es[i]? = some ev) (hp : P ev = true) (hie : i ≤ e) :
    (es.take i).countP P + 1 ≤ (es.take (e + 1)).countP P := by
  have h1 : (es.take (i + 1)).countP P = (es.take i).countP P + 1 := by
    rw [List.take_add_one, hev, Option.toList_some, List.countP_append]
    simp [hp]
  have h2 := (List.take_sublist_take_left (l := es) (by omega : i + 1 ≤ e + 1)).countP_le
    (p := P)
  omega

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- **A named barrier is a hand-off from its participants to its `bar.sync` participants** of
one CTA. The participants arrive by either form; the consumers `syncs` arrive by `bar.sync` only
(`hsync`); a participant that exits has arrived `N` times while none arrives more often (`hN`,
`hexit`: the barrier's schedule). The producer's use is the barrier's arrivals up to and including
the event, the consumer's those before the event. A CTA barrier is the named barrier `0` of every
warp. -/
theorem of_bar (hX : Consistent L K A mem0 X) {count : Option Nat} {p : Finset Nat} {id : Nat}
    (hS : NamedBar.Sources L X count p id) (hG : NamedBar.Shape L count p id)
    {syncs : Nat → Prop}
    (hsync : ∀ h j pc cnt mode, syncs h → X.get (h, j) = some ⟨pc, .bar id cnt mode⟩ →
      mode = .sync)
    {N : Nat}
    (hN : ∀ g, g < L.threads → (g % L.block) / 32 ∈ p →
      (X.tr g).countP (Execution.isBarId id) ≤ N)
    (hexit : ∀ g, g < L.threads → (g % L.block) / 32 ∈ p →
      (∃ j pc, X.get (g, j) = some ⟨pc, .exit⟩) → (X.tr g).countP (Execution.isBarId id) = N) :
    Handoff L X (fun g h => SameCta L g h ∧ (g % L.block) / 32 ∈ p ∧ syncs h)
      (fun i => ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId id))
      (fun i => ((X.tr i.1).take i.2).countP (Execution.isBarId id)) := by
  rintro g h e f ⟨hsame, hpg, hsh⟩ hf hlt
  simp only at hlt
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hht : h < L.threads := hsame.2.1
  -- the consumer's barrier of ordinal `q`
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id)
    (show q + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId id) by omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    have hmj := hsync h j pcj cntj modej hsh hgetj
    subst hmj
    have hfb : X.IsBarrier (h, j) idj cntj pcj := hgetj
    have hph : (h % L.block) / 32 ∈ p := (hS.sync hfb hht).1
    -- the producer's arrival of the same ordinal
    obtain ⟨i, pci, mi, hbi, hci⟩ := hS.member_arrival_any hX hG hfb (by simp only; omega)
      (show g / L.block = h / L.block from hsame.2.2) hpg (by
        rintro hex
        have hall := hexit g hgt hpg hex
        have hle := hN h hht hph
        have hge : q + 1 ≤ (X.tr g).countP (Execution.isBarId idj) := by
          have h1 := (List.take_sublist f (X.tr h)).countP_le (p := Execution.isBarId idj)
          omega
        obtain ⟨i, ev', hi, hbi, hci⟩ :=
          MbarRing.Slot.exists_nth_countP (Execution.isBarId idj) hge
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi cnti modei =>
          simp only [Execution.isBarId, beq_iff_eq] at hbi
          subst hbi
          have hcnti := (hS (g, i) pci cnti ⟨modei, hi⟩ hgt).2
          subst hcnti
          exact ⟨i, pci, modei, hi, by simp only; omega⟩
        | _ => simp [Execution.isBarId] at hbi)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId idj) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle
      have h1 := countP_take_succ_ge (P := Execution.isBarId idj) (es := X.tr g) (e := e) hbi
        (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.Sources.arrive_sync_baseCausality hX hS hG hsame hbi hfb (by omega)
      (by omega) hei hjf hf
  | _ => simp [Execution.isBarId] at hbj

/-- **A named barrier's first `n` instances are a hand-off** (Inkling request L-m): as `of_bar`,
with the consumer's use capped at `n`, and of the barrier's schedule only that a participant that
exits has arrived at least `n` times (`hexit`), a fact about each thread's events up to its `n`-th
arrival. A kernel whose role choice reads a word written before an early CTA barrier uses it with
a first following stage that ignores the word, before the whole schedule is known. -/
theorem of_bar_upTo (hX : Consistent L K A mem0 X) {count : Option Nat} {p : Finset Nat} {id : Nat}
    (hS : NamedBar.Sources L X count p id) (hG : NamedBar.Shape L count p id)
    {syncs : Nat → Prop}
    (hsync : ∀ h j pc cnt mode, syncs h → X.get (h, j) = some ⟨pc, .bar id cnt mode⟩ →
      mode = .sync)
    (n : Nat)
    (hexit : ∀ g, g < L.threads → (g % L.block) / 32 ∈ p →
      (∃ j pc, X.get (g, j) = some ⟨pc, .exit⟩) → n ≤ (X.tr g).countP (Execution.isBarId id)) :
    Handoff L X (fun g h => SameCta L g h ∧ (g % L.block) / 32 ∈ p ∧ syncs h)
      (fun i => ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId id))
      (fun i => min (((X.tr i.1).take i.2).countP (Execution.isBarId id)) n) := by
  rintro g h e f ⟨hsame, hpg, hsh⟩ hf hlt0
  simp only at hlt0
  have hlt : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) <
      ((X.tr h).take f).countP (Execution.isBarId id) := lt_of_lt_of_le hlt0 (Nat.min_le_left _ _)
  have hltn : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) < n :=
    lt_of_lt_of_le hlt0 (Nat.min_le_right _ _)
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hht : h < L.threads := hsame.2.1
  -- the consumer's barrier of ordinal `q`
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id)
    (show q + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId id) by omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    have hmj := hsync h j pcj cntj modej hsh hgetj
    subst hmj
    have hfb : X.IsBarrier (h, j) idj cntj pcj := hgetj
    have hph : (h % L.block) / 32 ∈ p := (hS.sync hfb hht).1
    -- the producer's arrival of the same ordinal
    obtain ⟨i, pci, mi, hbi, hci⟩ := hS.member_arrival_any hX hG hfb (by simp only; omega)
      (show g / L.block = h / L.block from hsame.2.2) hpg (by
        rintro hex
        have hall := hexit g hgt hpg hex
        have hge : q + 1 ≤ (X.tr g).countP (Execution.isBarId idj) := by omega
        obtain ⟨i, ev', hi, hbi, hci⟩ :=
          MbarRing.Slot.exists_nth_countP (Execution.isBarId idj) hge
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi cnti modei =>
          simp only [Execution.isBarId, beq_iff_eq] at hbi
          subst hbi
          have hcnti := (hS (g, i) pci cnti ⟨modei, hi⟩ hgt).2
          subst hcnti
          exact ⟨i, pci, modei, hi, by simp only; omega⟩
        | _ => simp [Execution.isBarId] at hbi)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId idj) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle
      have h1 := countP_take_succ_ge (P := Execution.isBarId idj) (es := X.tr g) (e := e) hbi
        (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.Sources.arrive_sync_baseCausality hX hS hG hsame hbi hfb (by omega)
      (by omega) hei hjf hf
  | _ => simp [Execution.isBarId] at hbj

end Handoff

/-! ### Regions ordered by items -/

/-- **The item order of a region**: conflicting accesses of one item at a byte of the region are
ordered one way or the other; those of an earlier item are visible to those of a later one. -/
structure ItemOrder (L : Launch) (X : Execution) (R : Loc → Prop) (item : AsyncCopy.Ref → Nat) :
    Prop where
  /-- Conflicting accesses of one item are ordered. -/
  same : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → item e = item f →
    modelCausality L X l e f ∨ modelCausality L X l f e
  /-- An access of an earlier item is visible to a conflicting access of a later item. -/
  later : ∀ e f a b l, Conflict X e f a b → a.Covers l → b.Covers l → R l → item e < item f →
    modelCausality L X l e f

/-- A conflict is symmetric. -/
theorem conflict_symm {e f : AsyncCopy.Ref} {a b : Acc} (h : Conflict X e f a b) :
    Conflict X f e b a := by
  obtain ⟨hne, we, wf, he, hf, hw, hov⟩ := h
  exact ⟨fun h => hne h.symm, wf, we, hf, he, hw.symm, hov.symm⟩

/-- **A region with an item order has its conflicts ordered.** -/
theorem ItemOrder.ordered {R : Loc → Prop} {item : AsyncCopy.Ref → Nat}
    (h : ItemOrder L X R item) : ConflictsOrdered L X R := by
  intro e f a b l hc ha hb hl
  rcases Nat.lt_trichotomy (item e) (item f) with hlt | heq | hgt
  · exact .inl (h.later e f a b l hc ha hb hl hlt)
  · exact h.same e f a b l hc ha hb hl heq
  · exact .inr (h.later f e b a l (conflict_symm hc) hb ha hl hgt)

/-- **A region of thread accesses ordered by a hand-off.** Every access of a byte of the region is
a thread's (`hcov`); of two conflicting accesses of different items, the earlier item's thread
hands off to the later's with the earlier event's producer use below the later's consumer use
(`hlt`); conflicting accesses of one item are one thread's (`heq`). -/
theorem ConflictsOrdered.of_handoff {R : Loc → Prop} {pair : Nat → Nat → Prop}
    {up uq : EvId → Nat} (H : Frame.Handoff L X pair up uq) (item : EvId → Nat)
    (hcov : ∀ ref a w l, X.Intent ref a w → a.Covers l → R l → ∃ i, ref = .thread i)
    (hlt : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → item i < item j → pair i.1 j.1 ∧ up i < uq j)
    (heq : ∀ i j a b w w' l, X.Access i a w → X.Access j b w' → (w = true ∨ w' = true) →
      a.Covers l → b.Covers l → R l → item i = item j → i.1 = j.1) :
    ConflictsOrdered L X R := by
  intro e f a b l hc ha hb hl
  obtain ⟨hne, w, w', hi, hj, hw, hov⟩ := hc
  obtain ⟨i, rfl⟩ := hcov e a w l hi ha hl
  obtain ⟨j, rfl⟩ := hcov f b w' l hj hb hl
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hlen : ∀ {x : EvId} {c : Acc} {v : Bool}, X.Access x c v → x.2 < (X.tr x.1).length :=
    fun hx => hx.lt
  rcases Nat.lt_trichotomy (item i) (item j) with h1 | h1 | h1
  · obtain ⟨hp, hu⟩ := hlt i j a b w w' l hi hj hw ha hb hl h1
    exact .inl (.inl (H i.1 j.1 i.2 j.2 hp (hlen hj) hu))
  · have hs := heq i j a b w w' l hi hj hw ha hb hl h1
    have h2 : i.2 ≠ j.2 := fun h => hij (Prod.ext hs h)
    rcases Nat.lt_or_gt_of_ne h2 with h3 | h3
    · exact .inl (.inl (.single (.inl (po_of_overlap hi hj hs h3 hov))))
    · exact .inr (.inl (.single (.inl (po_of_overlap hj hi hs.symm h3 hov.symm))))
  · obtain ⟨hp, hu⟩ := hlt j i b a w' w l hj hi hw.symm hb ha hl h1
    exact .inr (.inl (H j.1 i.1 j.2 i.2 hp (hlen hi) hu))

end PTX.Frame
