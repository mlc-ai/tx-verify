-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Core.Assembly.WaitOrder
public import Lemmas.Order.JointWaits
public import Core.Assembly.Execution
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Tensor.TensorDescriptor
public import Mathlib.Data.Fintype.Card
public import Lemmas.Async.AsyncCopy

@[expose] public section

/-! # Waits paths

Tools for the execution-order axioms of `Consistent` (MEM-OBJECT-ORDER-CAUSALITY, DEP-ORDER). Every
`stageCausality`, `ObjectOrder`, `SyncObserved` and `DepStep` edge is a `Waits` path, and so is
`baseCausality` between present events (`baseCausality_base_waits`, `baseCausality_waits_present`),
so a node set that no `Waits` edge leaves is closed under all of them (used by the extension lemmas
in `Lemmas/Order/WaitingClosure.lean`). `ObjectCoherent` gives one mbarrier's own history the order
of causality at the pairs of the synchronizing part of that object's order; no other object's order
is used (`ObjectCoherent.index_lt`, `ObjectCoherent.thread_index_lt`,
`ObjectCoherent.same_thread_index_lt`). -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

/-- Program order as a path of issue/return nodes, for any relation that has each node's
issue-to-return edge and each return-to-next-issue edge. -/
theorem po_path {R : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop}
    (node : ∀ i : EvId, i.2 < (X.tr i.1).length → R (.thread i, false) (.thread i, true))
    (step : ∀ i j : EvId, i.1 = j.1 → j.2 = i.2 + 1 → j.2 < (X.tr j.1).length →
      R (.thread i, true) (.thread j, false))
    {i j : EvId} (h : i.1 = j.1 ∧ i.2 < j.2 ∧ j.2 < (X.tr j.1).length) :
    Relation.TransGen R (.thread i, true) (.thread j, false) := by
  obtain ⟨t, k⟩ := i
  obtain ⟨t', n⟩ := j
  obtain ⟨hij, hlt, hj⟩ := h
  simp only at hij hlt hj
  subst hij
  induction n with
  | zero => omega
  | succ n ih =>
    have e := step (t, n) (t, n + 1) rfl rfl hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | rfl
    · exact ((ih hlt (by omega)).tail (node (t, n) (show n < (X.tr t).length by omega))).tail e
    · exact .single e

theorem Waits.trace {i j : EvId} (h : i.1 = j.1 ∧ i.2 < j.2 ∧ j.2 < (X.tr j.1).length) :
    Relation.TransGen (Waits L X) (.thread i, true) (.thread j, false) :=
  po_path (fun _ hi => Waits.node (present_of_len hi))
    (fun i j h1 h2 h3 => .inr (.inl ⟨rfl, rfl, i, j, rfl, rfl, h1, h2, h3⟩)) h

theorem Waits.po {i j : EvId} (h : po X i j) :
    Relation.TransGen (Waits L X) (.thread i, true) (.thread j, false) :=
  Waits.trace ⟨h.1, h.2.1, h.2.2.1⟩

theorem Waits.before {m : Loc} {e f : AsyncCopy.Ref} (h : MBarrier.Before (X.objects m) e f) :
    Waits L X (e, true) (f, true) :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, m, h⟩))))))

theorem before_of_update {log : List (MBarrier.Record AsyncCopy.Ref)} {x w : AsyncCopy.Ref}
    (h : MBarrier.UpdateBeforeWait log x w) : MBarrier.Before log x w := by
  obtain ⟨k, l, r, s, _, hr, hrid, _, hs, hsid, _, _, hkl, _, _, _⟩ := h
  exact ⟨k, l, r, s, hr, hrid, hs, hsid, hkl⟩

/-- An issue action of the bulk-group action list names the event at its own position. -/
theorem bulkAction_issue {g index : Nat} {k : Kind} {i : EvId}
    (h : bulkAction g index k = some (.issue i)) : i = (g, index) := by
  cases k <;> simp only [bulkAction] at h
  all_goals try split_ifs at h
  all_goals first
    | exact (BulkGroup.Action.issue.inj (Option.some.inj h)).symm
    | simp_all

/-- An issue action of the `cp.async`-group action list names the event at its own position. -/
theorem asyncAction_issue {g index : Nat} {k : Kind} {i : EvId}
    (h : asyncAction g index k = some (.issue i)) : i = (g, index) := by
  cases k <;> simp only [asyncAction] at h
  all_goals try split_ifs at h
  all_goals first
    | exact (BulkGroup.Action.issue.inj (Option.some.inj h)).symm
    | simp_all

/-- A group wait covers an event of its own thread's trace prefix: the covered operation is an
earlier event of the waiting thread. -/
theorem GroupWaitsFor.index {i j : EvId} {k : GroupWait} (h : GroupWaitsFor X k i j) :
    i.1 = j.1 ∧ i.2 < j.2 := by
  obtain ⟨gj, jj⟩ := j
  cases k with
  | bulk mode =>
    obtain ⟨pc, rem, -, hobs⟩ := h
    obtain ⟨⟨ev, idx⟩, hmem, hk⟩ := List.mem_filterMap.mp (BulkGroup.issue_of_observes hobs)
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    have hidx : idx < jj :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hmem).1 (List.length_take_le jj (X.tr gj))
    have hie : i = (gj, idx) := bulkAction_issue hk
    subst hie
    exact ⟨rfl, hidx⟩
  | cpAsync =>
    obtain ⟨pc, rem, -, hobs⟩ := h
    obtain ⟨⟨ev, idx⟩, hmem, hk⟩ := List.mem_filterMap.mp (BulkGroup.issue_of_observes hobs)
    rw [List.mem_zipIdx_iff_getElem?] at hmem
    have hidx : idx < jj :=
      Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hmem).1 (List.length_take_le jj (X.tr gj))
    have hie : i = (gj, idx) := asyncAction_issue hk
    subst hie
    exact ⟨rfl, hidx⟩

/-- A stage of an operation that a group wait covers fills a need of the wait's return: the group
wait waits for the stages `GroupWaitStages` of every operation it covers (DEP-ORDER). -/
theorem GroupWaitsFor.witness {i j : EvId} {k : GroupWait} {p : AsyncCopy.Part}
    (h : GroupWaitsFor X k i j) (hp : p ∈ GroupWaitStages X i k) (hpres : X.AsyncPresent i p) :
    Witness L X (.async i p) j := by
  obtain ⟨gi, ii⟩ := i
  obtain ⟨gj, jj⟩ := j
  obtain ⟨hi1, hi2⟩ := h.index
  subst hi1
  have hneed : Need.node (· = .async (gi, ii) p) ∈ Needs L X (gi, jj) := by
    cases k with
    | bulk mode =>
      obtain ⟨pc, rem, hget, hobs⟩ := h
      simp only [Needs, hget, KindNeeds, groupNeeds, needsIf]
      refine List.mem_flatMap.mpr ⟨ii, List.mem_range.mpr hi2, ?_⟩
      rw [ite_eq_left (show GroupWaitsFor X (.bulk mode) (gi, ii) (gi, jj) from
        ⟨pc, rem, hget, hobs⟩)]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    | cpAsync =>
      obtain ⟨pc, rem, hget, hobs⟩ := h
      simp only [Needs, hget, KindNeeds, groupNeeds, needsIf]
      refine List.mem_flatMap.mpr ⟨ii, List.mem_range.mpr hi2, ?_⟩
      rw [ite_eq_left (show GroupWaitsFor X .cpAsync (gi, ii) (gi, jj) from ⟨pc, rem, hget, hobs⟩)]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact Witness.of_need L hneed hpres rfl

/-- Each synchronizes-with, program-order or fence edge of `baseCausality` is a `Waits` path from
the source's return to the target's issue. -/
theorem baseCausality_base_waits {e f : EvId}
    (h : po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
      WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) :
    Relation.TransGen (Waits L X) (.thread e, true) (.thread f, false) ∧
      X.RefPresent (.thread f) := by
  rcases h with h | ⟨hsc, key, i, j, hi, hj, hei, hjf, hf⟩ |
      ⟨x, w, m, rs, as, ⟨tx, count, pc, hx⟩, ⟨⟨pcw, par, hw⟩, hu⟩, _, hwf1, hwf2, hf, hxe, hex⟩ |
      ⟨_, i, j, ⟨phase, ha, hwo⟩, hil, hei, hjf, hf⟩ |
      ⟨i, j, ⟨hsw, mask, inst, ⟨pci, hi⟩, ⟨pcj, hj⟩⟩, hei, hjf, hf⟩ | h | h
  · exact ⟨Waits.po h, present_of_len h.2.2.1⟩
  · obtain ⟨_, ⟨_, pci, _, hbi⟩, _⟩ := id hi
    obtain ⟨_, ⟨_, pcj, hbj⟩, _⟩ := id hj
    refine ⟨((Waits.trace (L := L) (i := e) (j := (e.1, i)) ⟨rfl, hei, len_of_get hbi⟩).tail
      (.inr (.inr (.inl ⟨(e.1, i), (f.1, j), rfl, rfl, ⟨_, hbi⟩, ⟨_, hbj⟩,
        .inr (.inl ⟨rfl, rfl, hsc, key, hi, hj⟩)⟩)))).trans
      (Waits.trace (i := (f.1, j)) (j := f) ⟨rfl, hjf, hf⟩), present_of_len hf⟩
  · have before : Waits L X (.thread x, true) (.thread w, true) :=
      Waits.before (before_of_update hu)
    have after := Waits.trace (L := L) (X := X) (i := w) (j := f) ⟨hwf1, hwf2, hf⟩
    refine ⟨?_, present_of_len hf⟩
    rcases Nat.lt_or_eq_of_le hex with hlt | heq
    · exact (((Waits.trace (i := e) (j := x) ⟨hxe.symm, hlt, len_of_get hx⟩).tail
        (Waits.node ⟨_, hx⟩)).tail before).trans after
    · have : e = x := Prod.ext hxe.symm heq
      subst this
      exact .head before after
  · have hjl : j < (X.tr f.1).length := by omega
    refine ⟨((Waits.trace (L := L) (i := e) (j := (e.1, i)) ⟨rfl, hei, hil⟩).tail
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨(e.1, i), (f.1, j), rfl, rfl,
        present_of_len hil, present_of_len hjl,
        .inr (.inr (.inl ⟨rfl, rfl, phase, _, ha, hwo⟩))⟩))))))))).trans
      (Waits.trace (i := (f.1, j)) (j := f) ⟨rfl, hjf, hf⟩), present_of_len hf⟩
  · refine ⟨((Waits.trace (L := L) (i := e) (j := (e.1, i)) ⟨rfl, hei, len_of_get hi⟩).tail
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨rfl, rfl, (e.1, i), (f.1, j), rfl, rfl, hsw, mask, inst, ⟨pci, hi⟩,
          ⟨pcj, hj⟩⟩))))))))))).trans
      (Waits.trace (i := (f.1, j)) (j := f) ⟨rfl, hjf, hf⟩), present_of_len hf⟩
  · obtain ⟨_, _, _, _, _, hrd, -⟩ := id h
    have hedge : Waits L X (.thread e, true) (.thread f, false) :=
      .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl ⟨rfl, rfl, e, f, rfl, rfl, h⟩))))))))))
    obtain ⟨pc, hr⟩ | ⟨new, pc, hr⟩ := hrd
    · exact ⟨.single hedge, ⟨_, hr⟩⟩
    · exact ⟨.single hedge, ⟨_, hr⟩⟩
  · exact ⟨.single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inl ⟨rfl, rfl, e, f, rfl, rfl, h⟩)))))))))))))), present_of_len h.events.2⟩

/-- Base causality between thread instructions is a `Waits` path. -/
theorem baseCausality_waits_present {i j : EvId} (h : baseCausality L X i j) :
    Relation.TransGen (Waits L X) (.thread i, true) (.thread j, false) ∧
      X.RefPresent (.thread j) := by
  induction h with
  | single h => exact baseCausality_base_waits h
  | tail _ h ih =>
    obtain ⟨p, hp⟩ := baseCausality_base_waits h
    exact ⟨(ih.1.tail (Waits.node ih.2)).trans p, hp⟩

/-- Each stage-order edge is a `Waits` edge. -/
theorem StageOrder.waits {a c : AsyncCopy.Ref × Bool} (h : StageOrder X a c) : Waits L X a c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with ⟨rfl, rfl, rfl, hpres⟩ | ⟨rfl, rfl, h⟩
  · exact .inl ⟨rfl, rfl, rfl, hpres⟩
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl, h⟩⟩)))))

theorem CopyReleaseSync.waits {n : AsyncCopy.Ref} {f : EvId} (h : CopyReleaseSync L X n f) :
    Relation.TransGen (Waits L X) (n, true) (.thread f, false) := by
  obtain ⟨i, p, w, ws, rfl, hp, ⟨n, m, hn, -, hu⟩, -, hpo⟩ := h
  have hn' : n = .async i p := by rcases hp with rfl | rfl <;> exact hn.1
  subst hn'
  exact .head (Waits.before (before_of_update hu)) (Waits.po hpo)

/-- Each causal edge is a `Waits` path. -/
theorem stageCausality.waits {a c : AsyncCopy.Ref × Bool}
    (h : stageCausality L X a c) : Relation.TransGen (Waits L X) a c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with h | ⟨rfl, rfl, i, j, rfl, rfl, h⟩ | ⟨rfl, rfl, j, rfl, h⟩
  · exact .single (StageOrder.waits h)
  · exact (baseCausality_waits_present h).1
  · exact CopyReleaseSync.waits h

theorem bulk_present {mode : BulkGroup.WaitMode} {i w : EvId} (h : BulkWaitsFor X mode i w) :
    X.RefPresent (.thread w) := by
  obtain ⟨pc, _, hw, _⟩ := h
  exact ⟨_, hw⟩

/-- Each observation is a `Waits` path from the observed node to the observer's return. -/
theorem SyncObserved.waits {x w : AsyncCopy.Ref} (h : SyncObserved L X x w) :
    Relation.TransGen (Waits L X) (x, false) (w, true) := by
  rcases h with ⟨⟨hp, j, m, acq, ws, rfl, ⟨-, hu⟩, -⟩, j', m', pc, q, ws', us, g, hwj, -, -, -⟩ |
    ⟨i, p, j, k, rfl, rfl, hpres, hw, hstage⟩
  · obtain rfl := AsyncCopy.Ref.thread.inj hwj
    exact .tail (.single (Waits.node hp)) (Waits.before (before_of_update hu))
  · exact .single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (
      .inl ⟨rfl, rfl, j, rfl, hw.witness hstage hpres⟩)))))))))

theorem ObjectOrder.waits {o : OrderObject} {a c : AsyncCopy.Ref × Bool}
    (h : ObjectOrder L X o a c) : Waits L X a c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  cases o with
  | mbar m =>
    obtain ⟨rfl, rfl, h⟩ := h
    exact Waits.before h
  | ctaBar c id =>
    obtain ⟨hb, hb', i, j, he, hf, hp, hq, k, l, r, q, hr, hq', hkl, _, _, hi, hj⟩ := h
    exact .inr (.inr (.inl ⟨i, j, he, hf, hp, hq,
      .inl ⟨hb, hb', c, k, l, r, q, hr, hq', hkl, hi, hj⟩⟩))
  | cluster c =>
    obtain ⟨i, j, he, hf, hp, hq, k, l, r, q, hr, hq', hkl, hi, hj, hb, hb'⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨i, j, he, hf, hp, hq, .inl ⟨c, k, l, r, q, hr, hq', hkl, hi, hj, hb, hb'⟩⟩)))))))
  | tmem cta =>
    obtain ⟨hb, hb', i, j, he, hf, h⟩ := h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl ⟨hb, hb', i, j, he, hf, cta, h⟩))))))))))))

/-- Each dependency edge is a `Waits` path. -/
theorem DepStep.waits {K : Kernel} {a c : AsyncCopy.Ref × Bool}
    (h : DepStep L K X a c) : Relation.TransGen (Waits L X) a c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases h with h | h | ⟨rfl, rfl, j, rfl, h⟩ | ⟨rfl, rfl, w, j, rfl, rfl, h⟩
  · exact .single (StageOrder.waits h)
  · have hb : b = false := h.1
    have hb' : b' = false := h.2.1
    exact .single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (
      .inr (.inr ⟨hb, hb', h⟩))))))))))))))
  · exact .single (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl ⟨rfl, rfl, j, rfl, h⟩)))))))))
  · exact Waits.trace h.1

end

/-- MEM-OBJECT-ORDER-CAUSALITY: causality with the order of one object has no cycle. -/
theorem Consistent.objectCoherent {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) : ObjectCoherent L X :=
  hX.object

/-- Causality together with the synchronizing part of one object's order. -/
abbrev WithObject (L : Launch) (X : Execution) (o : OrderObject) :
    AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop :=
  fun a c => stageCausality L X a c ∨ SyncObjectOrder L X o a c

/-- A dependency through causality and the synchronizing part of this object's order forces the
order of two records of the object's history, when the reverse pair of the two records is in that
synchronizing part (MEM-OBJECT-ORDER-CAUSALITY, EXT-OBJECT-ORDER: a pair of synchronizing records,
a pair with the initialization or invalidation, or a pair of one thread). -/
theorem ObjectCoherent.index_lt {L : Launch} {X : Execution} (h : ObjectCoherent L X)
    {m : Loc} {i j : Nat} {ri rj : MBarrier.Record AsyncCopy.Ref}
    (hi : (X.objects m)[i]? = some ri) (hj : (X.objects m)[j]? = some rj)
    (hs : ObjectOrder L X (.mbar m) (rj.id, true) (ri.id, true) →
      SyncObjectOrder L X (.mbar m) (rj.id, true) (ri.id, true))
    (hd : Relation.TransGen (WithObject L X (.mbar m)) (ri.id, true) (rj.id, true)) : i < j := by
  by_contra hn
  rcases Nat.eq_or_lt_of_le (by omega : j ≤ i) with heq | hlt
  · subst j
    rw [hi] at hj
    cases hj
    exact h _ _ hd
  · exact h _ _ (hd.tail (.inr (hs ⟨rfl, rfl, j, i, rj, ri, hj, rfl, hi, rfl, hlt⟩)))

/-- Causality between two thread operations is respected by their records on one object, when the
reverse pair of the two records is in the synchronizing part of the object's order. Two records
of one thread always are (`ObjectCoherent.same_thread_index_lt`). -/
theorem ObjectCoherent.thread_index_lt {L : Launch} {X : Execution} (h : ObjectCoherent L X)
    {m : Loc} {i j : Nat} {ri rj : MBarrier.Record AsyncCopy.Ref} {e f : EvId}
    (hi : (X.objects m)[i]? = some ri) (hj : (X.objects m)[j]? = some rj)
    (hs : ObjectOrder L X (.mbar m) (rj.id, true) (ri.id, true) →
      SyncObjectOrder L X (.mbar m) (rj.id, true) (ri.id, true))
    (hei : ri.id = .thread e) (hfj : rj.id = .thread f)
    (hp : Relation.TransGen (stageCausality L X) (.thread e, true) (.thread f, true)) : i < j := by
  apply h.index_lt hi hj hs
  rw [hei, hfj]
  exact Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hp

/-- Causality between two operations of one thread is respected by their records on one
object: a pair of records of one thread is in the synchronizing part of the object's order. -/
theorem ObjectCoherent.same_thread_index_lt {L : Launch} {X : Execution}
    (h : ObjectCoherent L X) {m : Loc} {i j : Nat} {ri rj : MBarrier.Record AsyncCopy.Ref}
    {e f : EvId} (hi : (X.objects m)[i]? = some ri) (hj : (X.objects m)[j]? = some rj)
    (hei : ri.id = .thread e) (hfj : rj.id = .thread f) (hef : e.1 = f.1)
    (hp : Relation.TransGen (stageCausality L X) (.thread e, true) (.thread f, true)) :
    i < j :=
  h.thread_index_lt hi hj (fun ho => ⟨ho, .inr (.inr (.inr ⟨f, e, by rw [hfj], by rw [hei],
    hef.symm⟩))⟩) hei hfj hp

end

end PTX
