-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierPhase

@[expose] public section

/-! # An object's state after its initialization

A proof tool. Once an object is initialized, every later record of its checked history, failed
or not, keeps it initialized with the same expected count (`checked_expected_after_init`). An
object whose first record is a successful initialization therefore has, before any of its
records, either no earlier records (the initialization itself) or a state
(`first_or_initialized`). Only that object's own history is used. -/

namespace PTX.ObjectInit
open MBarrier


/-- Every successful operation on an initialized object preserves its expected
arrival count. Phase advancement changes pending arrivals, not that count. -/
theorem perform_some_expected {s : State} {a : Action} {reply : Reply}
    (hp : perform (some s) a=.ok reply) (hni : a ≠ .inval) :
    ∃ t,reply.state=some t ∧ t.expected=s.expected := by
  cases a <;> simp [perform,bind,Except.bind,pure,Except.pure,throw,throwThe,
    MonadExceptOf.throw] at hp
  · split_ifs at hp
    simp at hp
    subst hp
    refine ⟨_,rfl,?_⟩
    unfold advance
    split_ifs <;> rfl
  · split_ifs at hp
    simp at hp
    subst hp
    refine ⟨_,rfl,?_⟩
    unfold advance
    split_ifs <;> rfl
  · split_ifs at hp
    simp at hp
    subst hp
    exact ⟨_,rfl,rfl⟩
  · subst hp
    exact ⟨_,rfl,rfl⟩
  · exact absurd rfl hni

/-- The invariant also covers faults: RecordOk gives an error record the exact
pre-state as its reply, rather than deleting the operation. -/
theorem recordOk_some_expected {ι : Type} {s : State} {r : Record ι}
    (hr : RecordOk (some s) r) (hni : r.action ≠ .inval) :
    ∃ t,r.reply.state=some t ∧ t.expected=s.expected := by
  unfold RecordOk at hr
  cases hp : perform (some s) r.action with
  | error fault =>
    rw [hp] at hr
    exact ⟨s,hr.1 ▸ rfl,rfl⟩
  | ok reply =>
    rw [hp] at hr
    obtain ⟨t,ht,hexpected⟩ := perform_some_expected hp hni
    exact ⟨t,hr.1 ▸ ht,hexpected⟩

/-- An arbitrary checked suffix preserves initialization and expected count.
This induction includes every successful and faulting record in the suffix. -/
theorem history_some_expected {ι : Type} {initial final : Option State}
    {log : List (Record ι)} (h : RecordedHistory initial log final) (hni : NoInval log)
    {s : State} (hs : initial=some s) :
    ∃ t,final=some t ∧ t.expected=s.expected := by
  induction h generalizing s with
  | nil => exact ⟨s,hs,rfl⟩
  | @cons s0 r rest t0 hr _ ih =>
    subst hs
    obtain ⟨middle,hm,he⟩ := recordOk_some_expected hr (hni r List.mem_cons_self)
    obtain ⟨t,ht,hte⟩ := ih (fun q hq => hni q (List.mem_cons_of_mem _ hq)) hm
    exact ⟨t,ht,hte.trans he⟩

/-- Between any two checked-log positions, an existing object remains present
with the same expected count. The endpoint may be exactly log.length. -/
theorem checked_expected_after {ι : Type} {log : List (Record ι)}
    (h : CheckedLog log) (hni : NoInval log) {i j : Nat} (hij : i≤j) (hj : j≤log.length)
    {s : State} (hs : stateBefore log i=some s) :
    ∃ t,stateBefore log j=some t ∧ t.expected=s.expected := by
  have hp := h.prefix hj
  rw [←List.take_append_drop i (log.take j)] at hp
  obtain ⟨middle,hm,hrest⟩ := hp.split
  rw [List.take_take,Nat.min_eq_left hij] at hm
  rw [hm.unique (h.prefix (Nat.le_trans hij hj)),hs] at hrest
  exact history_some_expected hrest
    (fun q hq => hni q (List.mem_of_mem_take (List.mem_of_mem_drop hq))) rfl

/-- A genuinely successful initialization has the canonical initial reply.
The conclusion is derived from RecordOk, the actual init action and its fault
field; it assumes neither a unique initializer nor a fault-free prefix. -/
theorem recordOk_successful_init_reply {ι : Type} {before : Option State}
    {r : Record ι} {count : Nat} (hr : RecordOk before r)
    (ha : r.action=.init count) (hf : r.fault=none) :
    before=none ∧ validCount count ∧
      r.reply=⟨some ⟨0,count,count,0,true⟩,none,none⟩ := by
  cases before with
  | none =>
    by_cases hc : validCount count
    · have hh := hr
      simp [RecordOk,ha,perform,validCount,hc,pure,Except.pure] at hh
      exact ⟨rfl,hc,hh.1⟩
    · simp [RecordOk,ha,perform,hc,hf,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hr
  | some s =>
    simp [RecordOk,ha,perform,hf,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at hr

/-- A canonical initReply at index k fixes the expected count before every
later position through the end of the log. No later record is required at j. -/
theorem checked_expected_after_init_reply {ι : Type} {log : List (Record ι)}
    (h : CheckedLog log) (hni : NoInval log) {k j count : Nat} {r : Record ι}
    (hk : log[k]?=some r)
    (hreply : r.reply=⟨some ⟨0,count,count,0,true⟩,none,none⟩)
    (hkj : k<j) (hj : j≤log.length) :
    ∃ s,stateBefore log j=some s ∧ s.expected=count := by
  have hs : stateBefore log (k+1)=some ⟨0,count,count,0,true⟩ := by
    simp [stateBefore,hk,hreply]
  exact checked_expected_after h hni (by omega) hj hs

/-- The same result when success is given by the real init action and fault
field, rather than by spelling its reply. Later re-init faults are allowed. -/
theorem checked_expected_after_init {ι : Type} {log : List (Record ι)}
    (h : CheckedLog log) (hni : NoInval log) {k j count : Nat} {r : Record ι}
    (hk : log[k]?=some r) (ha : r.action=.init count) (hf : r.fault=none)
    (hkj : k<j) (hj : j≤log.length) :
    ∃ s,stateBefore log j=some s ∧ s.expected=count := by
  have hreply := (recordOk_successful_init_reply (h.at hk) ha hf).2.2
  exact checked_expected_after_init_reply h hni hk hreply hkj hj

/-- Distinct operation identities identify their real record positions. -/
theorem checked_record_index_eq {ι : Type} {log : List (Record ι)}
    (h : CheckedLog log) {i j : Nat} {r q : Record ι}
    (hi : log[i]?=some r) (hj : log[j]?=some q) (hid : r.id=q.id) : i=j := by
  apply (List.Nodup.getElem?_inj (xs:=log.map Record.id)
    (by simpa using (List.getElem?_eq_some_iff.mp hi).1) h.1).mp
  simp only [List.getElem?_map,hi,hj]
  exact congrArg some hid

/-- A record of an object whose first record is a successful initialization: the
initialization is at position `0`, and every other record has a state before it. -/
theorem first_or_initialized {ι : Type} {log : List (Record ι)} (h : CheckedLog log)
    (hni : NoInval log)
    {i : Nat} {r r0 : Record ι} (hi : log[i]? = some r) (h0 : log[0]? = some r0) {count : Nat}
    (ha0 : r0.action = .init count) (hf0 : r0.fault = none) :
    (r.id = r0.id → i = 0) ∧ (r.id ≠ r0.id → ∃ s, stateBefore log i = some s) := by
  refine ⟨fun hid => checked_record_index_eq h hi h0 hid, fun hid => ?_⟩
  have hpos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0] at hi
      exact absurd (congrArg Record.id (Option.some.inj hi)).symm hid
    · exact hpos
  have hlt : i < log.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨s, hs, -⟩ := checked_expected_after_init h hni h0 ha0 hf0 hpos (Nat.le_of_lt hlt)
  exact ⟨s, hs⟩

end PTX.ObjectInit
