-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Order.WaitOrderWaits
public import Lemmas.Async.AsyncOrigins
public import Lemmas.Protocol.MbarInit
public import Lemmas.MBarrier.MBarrierAddress
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

section
/-! The records of one thread on one mbarrier object.

In one object's history, the records of one thread appear in the thread's program order
(`Consistent.object_thread_index_iff`): program order is causality, a pair of records of one
thread is in the synchronizing part of the object's order (`SyncObjectOrder`), and causality
together with that part has no cycle (`ObjectCoherent`). No other object's order is used.
Fault records are retained: this is an identity/index theorem, independent of object-transition
safety. -/
namespace PTX
noncomputable section
open AsyncCopy

/-- Selecting one physical source thread does not select its async effects. -/
def objectThreadSelected (g : Nat) : Ref → Bool
  | .thread e => e.1 == g
  | .async .. => false

theorem objectThreadSelected_iff {g : Nat} {id : Ref} :
    objectThreadSelected g id = true ↔ ∃ j, id = .thread (g,j) := by
  cases id with
  | thread e => cases e; simp [objectThreadSelected,Prod.ext_iff]
  | async => simp [objectThreadSelected]

/-- Program order between two thread instructions is a causal path between their
completion nodes. -/
theorem stageCausality.of_po {L : Launch} {X : Execution} {e f : EvId} (hp : po X e f) :
    Relation.TransGen (stageCausality L X) (.thread e, true) (.thread f, true) :=
  .tail (.single (b := (.thread f, false))
      (Or.inr (Or.inl ⟨rfl, rfl, e, f, rfl, rfl, .single (.inl hp)⟩)))
    (show stageCausality L X (.thread f, false) (.thread f, true) from
      Or.inl (Or.inl ⟨rfl, rfl, rfl, present_of_len hp.2.2.1⟩))

/-- The object record's identity names an actual source event, including when
its checked object transition reports a fault. -/
theorem Consistent.object_thread_record_present {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) {g k : Nat} (hid : r.id = .thread (g,k)) :
    ∃ ev, X.get (g,k) = some ev := by
  have hp := object_record_present hX.tma hr
  rw [hid] at hp
  exact hp

/-- For two records of this one thread, object order and source order agree. -/
theorem Consistent.object_thread_index_iff {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {i j g a b : Nat}
    {r s : MBarrier.Record Ref} (hi : (X.objects m)[i]? = some r)
    (hj : (X.objects m)[j]? = some s)
    (hr : r.id = .thread (g,a)) (hs : s.id = .thread (g,b)) :
    i < j ↔ a < b := by
  obtain ⟨ev,he⟩ := hX.object_thread_record_present (List.mem_of_getElem? hi) hr
  obtain ⟨fv,hf⟩ := hX.object_thread_record_present (List.mem_of_getElem? hj) hs
  have hpo (hab : a < b) : po X (g,a) (g,b) :=
    po_of_not_access rfl hab (len_of_get hf)
      (object_record_not_access hX.tma (List.mem_of_getElem? hj) hs)
  constructor
  · intro hij
    by_contra hn
    rcases Nat.eq_or_lt_of_le (by omega : b ≤ a) with hab | hba
    · have heq := ObjectInit.checked_record_index_eq (hX.tma.2.2.1 m).1 hi hj
        (by rw [hr,hs,hab])
      omega
    · have hlt := hX.objectCoherent.same_thread_index_lt hj hi hs hr rfl
        (stageCausality.of_po (show po X (g,b) (g,a) from
          po_of_not_access rfl hba (len_of_get he)
            (object_record_not_access hX.tma (List.mem_of_getElem? hi) hr)))
      omega
  · intro hab
    exact hX.objectCoherent.same_thread_index_lt hi hj hr hs rfl
      (stageCausality.of_po (hpo hab))

end
end PTX
end

section
/-! A successful object reply of a thread record is the thread's successful source wait on that
object. Source ok=true can name an explicit object fault, so the source-to-reply direction needs
that record's fault freedom. No global Safe or canonical protocol execution is assumed. -/
namespace PTX
noncomputable section
open AsyncCopy

/-- A successful checked reply cannot be an explicit object fault. This applies
to the current record without assuming anything about other object records. -/
theorem MBarrier.RecordOk.waited_no_fault {ι : Type} {before : Option MBarrier.State}
    {r : MBarrier.Record ι} (hr : MBarrier.RecordOk before r)
    (hw : r.reply.waited = some true) : r.fault = none := by
  unfold MBarrier.RecordOk at hr
  split at hr
  · exact hr.2
  · rw [hr.1] at hw
    cases hw

theorem MBarrier.CheckedLog.waited_no_fault {ι : Type}
    {log : List (MBarrier.Record ι)} (h : MBarrier.CheckedLog log)
    {j : Nat} {r : MBarrier.Record ι} (hj : log[j]? = some r)
    (hw : r.reply.waited = some true) : r.fault = none :=
  (h.at hj).waited_no_fault hw

/-- Counts a successful source wait on this exact object, at either scope. -/
def sourceWaitSuccess (m : Loc) (ev : Event) : Bool :=
  match ev.kind with
  | .wait target _ true _ _ => decide (target = m)
  | _ => false

private theorem sourceWaitSuccess_spec (m : Loc) (ev : Event) :
    sourceWaitSuccess m ev = match ev.kind with
      | .wait target _ ok _ _ => decide (target = m ∧ ok = true)
      | _ => false := by
  obtain ⟨pc,kind⟩ := ev
  cases kind <;> try rfl
  rename_i target parity ok acquire scope
  cases ok <;> simp [sourceWaitSuccess]

private theorem objectAction_thread_poll {X : Execution} {m : Loc} {g j p : Nat}
    (ha : objectAction X X.async m (.thread (g,j)) = some (.pollParity p true)) :
    ∃ pc acquire scope, X.get (g,j) = some ⟨pc,.wait m p true acquire scope⟩ := by
  obtain ⟨ev,he⟩ := objectAction_present ha
  obtain ⟨pc,kind⟩ := ev
  cases kind <;> simp only [objectAction,he] at ha
  case mbInit | arrive | mbInval => split_ifs at ha; cases ha
  case asyncArrive m' noinc =>
    cases noinc
    · simp only at ha; split_ifs at ha; cases ha
    · cases ha
  case wait target parity ok acquire scope =>
    split_ifs at ha with hm
    · have hap := Option.some.inj ha
      cases hap
      subst target
      exact ⟨pc,acquire,scope,he⟩
  all_goals cases ha

/-- Checked successful replies have actual successful source waits. The reverse
direction needs precisely this record's fault-free fact, not global safety. -/
theorem Consistent.object_thread_waited_iff {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) {g j : Nat} (hid : r.id = .thread (g,j))
    (hclean : r.fault = none) :
    r.reply.waited = some true ↔ (X.get (g,j)).any (sourceWaitSuccess m) = true := by
  have hmatch := (hX.tma.2.2.1 m).2.1 r hr
  have haction : objectAction X X.async m (.thread (g,j)) = some r.action := by
    simpa only [hid] using hmatch.1
  constructor
  · intro hw
    obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_,p,_,ha,_,_⟩ := ((hX.tma.2.2.1 m).1).okPoll hi hw
    obtain ⟨pc,acquire,scope,he⟩ := objectAction_thread_poll (ha ▸ haction)
    simp [he,sourceWaitSuccess]
  · intro hs
    cases he : X.get (g,j) with
    | none => simp only [he,Option.any_none,Bool.false_eq_true] at hs
    | some ev =>
      obtain ⟨pc,kind⟩ := ev
      cases kind <;> simp only [he,Option.any_some,sourceWaitSuccess_spec,Bool.false_eq_true] at hs
      rename_i target parity ok acquire scope
      have ht : target = m ∧ ok = true := of_decide_eq_true hs
      obtain ⟨rfl,rfl⟩ := ht
      have ha : r.action = .pollParity parity true := by
        have hh : some (.pollParity parity true) = some r.action := by
          simpa only [objectAction,he,↓reduceIte] using haction
        exact (Option.some.inj hh).symm
      exact hmatch.2 parity true ha hclean

/-- A generic form useful when source ordinal lemmas count by countP. -/
theorem MBarrier.selectedCount_eq_countP {ι : Type} (selected : ι → Bool)
    (log : List (MBarrier.Record ι)) :
    MBarrier.selectedCount selected log =
      log.countP (fun r => decide (selected r.id = true ∧ r.reply.waited = some true)) := by
  induction log with
  | nil => rfl
  | cons r rest ih =>
    by_cases h : selected r.id = true ∧ r.reply.waited = some true <;>
      simp [MBarrier.selectedCount,MBarrier.observerIncrement,ih,h,Nat.add_comm]

end
end PTX
end
