-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Order.ObjectOrder
public import Lemmas.Protocol.MbarInit
public import Lemmas.Order.StageCausalityThread
public import Lemmas.Async.AsyncOrigins

@[expose] public section

/-! # An mbarrier history follows causality

A proof tool for EXT-ASYNC-OBJECT (`AsyncObjectOrdered`). An initialization, invalidation or
observing acquire wait of mbarrier `m` whose operation causally precedes the issue of an
asynchronous operation lies before that operation's update of `m` in `m`'s history
(`Consistent.async_index_gt`), so a record whose thread operation happens before the issuer of
another record precedes it when the pair is one the object order keeps
(`Consistent.index_lt_of_baseCausality`); one operation has one position
(`Consistent.object_index_eq`, from `Lemmas/Order/ObjectOrder`). Only `m`'s own history is used. -/

namespace PTX
open AsyncCopy

/-- A record of `m` whose record point causally precedes the issue of instruction `i` comes
before, in `m`'s history, any update of `m` by `i`'s asynchronous operation, when the record is
the initialization or invalidation of `m` or an acquire wait observing that update
(EXT-ASYNC-OBJECT). -/
theorem Consistent.async_index_gt {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {m : Loc} {j k : Nat}
    {y d : MBarrier.Record Ref} (hj : (X.objects m)[j]? = some y)
    (hk : (X.objects m)[k]? = some d) {i : EvId} {p : Part} (hid : d.id = .async i p)
    (hne : y.id ≠ d.id)
    (hy : MbarLifetimeRecord X m y.id ∨
      ∃ w ws, y.id = .thread w ∧ AsyncCopy.WaitObserves X (.async i p) w m true ws)
    (hc : Relation.TransGen (stageCausality L X) (y.id, true) (.thread i, false)) : j < k := by
  by_contra hn
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hn) with heq | hlt
  · subst heq
    rw [hj] at hk
    exact hne (congrArg MBarrier.Record.id (Option.some.inj hk))
  · exact (hX.asyncObject m i p y.id ⟨k, j, d, y, hk, hid, hj, rfl, hlt⟩).2 hy hc

/-- A record whose thread operation happens before the issuer of another record of the same
object precedes it in that object's history: by causality for a thread record whose reverse pair
with the first record is in the synchronizing part of the object's order, and by EXT-ASYNC-OBJECT
for an asynchronous update when the first record is the object's initialization or invalidation
or an acquire wait observing the update. -/
theorem Consistent.index_lt_of_baseCausality {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {mb : Loc} {i j : Nat}
    {ri rj : MBarrier.Record Ref} {e : EvId}
    (hi : (X.objects mb)[i]? = some ri) (hj : (X.objects mb)[j]? = some rj)
    (hid : ri.id = .thread e) (hne : rj.id ≠ ri.id)
    (hs : ObjectOrder L X (.mbar mb) (rj.id, true) (ri.id, true) →
      SyncObjectOrder L X (.mbar mb) (rj.id, true) (ri.id, true))
    (hy : ∀ f q, rj.id = .async f q → MbarLifetimeRecord X mb ri.id ∨
      ∃ w ws, ri.id = .thread w ∧ AsyncCopy.WaitObserves X (.async f q) w mb true ws)
    (h : baseCausality L X e rj.id.issuer) : i < j := by
  have hc : Relation.TransGen (stageCausality L X) (ri.id, true) (.thread rj.id.issuer, false) :=
    hid ▸ .single (stageCausality.of_baseCausality h)
  have hp := object_record_present hX.tma (List.mem_of_getElem? hj)
  cases hr : rj.id with
  | thread f =>
    rw [hr] at hc hp
    exact hX.object.thread_index_lt hi hj hs hid hr
      (hid ▸ hc.tail (.inl (.inl ⟨rfl, rfl, rfl, hp⟩)))
  | async f q =>
    rw [hr] at hc hne
    exact hX.async_index_gt hi hj hr (Ne.symm (hr ▸ hne)) (hy f q hr) hc

end PTX
