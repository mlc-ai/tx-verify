-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.ObjectOrder
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Async.AsyncOrder
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.Tensor.TensorDescriptor
public import Core.MBarrier.InitPublication
public import Lemmas.Order.WaitOrderWaits

@[expose] public section

/-! # Initialization precedes every published user of an mbarrier object

A proof tool. An initialization `hb`-before the issue of a record's operation is before the
record in the object's history (`object_not_before_of_baseCausality`: causality with one object's
order for thread records, EXT-ASYNC-OBJECT for asynchronous ones), and an initialization that no
other record precedes is the object's first record. The restricted fence publication
(`InitFencePublished`, possibly through a relaxed cluster arrival) is not causality; it orders the
object's history through `Consistent.initFence` (OBJ-MBAR-INIT-PUBLICATION,
`object_not_before_of_init_fence`). -/

namespace PTX
open AsyncCopy MBarrier
noncomputable section

variable {K : Kernel} {L : Launch} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {m : Loc} {e : EvId} {count : Nat}

/-- The first object record precedes, in the object's history, no other record unless they
are the same operation. -/
theorem object_index_zero_of_not_before (hX : Consistent L K A mem0 X)
    {i : Nat} {r : Record Ref} (hi : (X.objects m)[i]? = some r)
    (hdeps : ∀ (j : Nat) (s : Record Ref), (X.objects m)[j]? = some s →
      s.id = r.id ∨ ¬ Before (X.objects m) s.id r.id) :
    i = 0 := by
  have hlen : 0 < (X.objects m).length :=
    lt_of_le_of_lt (Nat.zero_le i) (List.getElem?_eq_some_iff.mp hi).1
  let s := (X.objects m)[0]
  have hs : (X.objects m)[0]? = some s := List.getElem?_eq_getElem hlen
  rcases hdeps 0 s hs with heq | hnb
  · exact hX.object_index_eq hi hs heq.symm
  · by_contra hne
    exact hnb ⟨0, i, s, r, hs, rfl, hi, rfl, Nat.pos_of_ne_zero hne⟩

/-- The unique operation identities in a checked object log determine a unique
actual record index, even when the operation records an object fault. -/
theorem object_record_index_unique (ho : AsyncCopy.ObjectsOk X)
    {i j : Nat} {r s : Record Ref}
    (hi : (X.objects m)[i]? = some r) (hj : (X.objects m)[j]? = some s)
    (hid : r.id = s.id) : i = j := by
  apply (List.Nodup.getElem?_inj (xs := (X.objects m).map Record.id)
    (by simpa using (List.getElem?_eq_some_iff.mp hi).1) (ho m).1.1).mp
  simp only [List.getElem?_map,hi,hj]
  exact congrArg some hid

/-- Every actual initialization has its own checked record. RecordOk retains
the actual response or actual error; it does not discard invalid executions. -/
theorem init_record_of_objectsOk (ho : AsyncCopy.ObjectsOk X)
    (hinit : X.MbInit e m count) :
    ∃ i r, (X.objects m)[i]? = some r ∧ r.id = .thread e ∧
      r.action = .init count ∧ RecordOk (stateBefore (X.objects m) i) r ∧
      ∀ j s, (X.objects m)[j]? = some s → s.id = .thread e → j = i := by
  obtain ⟨pc,hget⟩ := hinit
  have ha : AsyncCopy.objectAction X X.async m (.thread e) = some (.init count) := by
    simp [AsyncCopy.objectAction,hget]
  obtain ⟨r,hr,hid⟩ := (ho m).2.2 (.thread e) (.init count) ha
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hr
  have haction : r.action = .init count := by
    have hm := ((ho m).2.1 r hr).1
    rw [hid,ha] at hm
    exact (Option.some.inj hm).symm
  refine ⟨i,r,hi,hid,haction,(ho m).1.at hi,?_⟩
  intro j s hj hs
  exact object_record_index_unique ho hj hi (hs.trans hid.symm)

theorem init_record_of_consistent {K : Kernel} {A : List Assumption}
    {L : Launch} {mem0 : Mem0} (hX : Consistent L K A mem0 X)
    (hinit : X.MbInit e m count) :
    ∃ i r, (X.objects m)[i]? = some r ∧ r.id = .thread e ∧
      r.action = .init count ∧ RecordOk (stateBefore (X.objects m) i) r ∧
      ∀ j s, (X.objects m)[j]? = some s → s.id = .thread e → j = i :=
  init_record_of_objectsOk hX.tma.2.2.1 hinit

/-- Explicitly supplying the real source event is enough to find its actual
record; no freshly constructed witness execution is used. -/
theorem init_record_of_actual_get {K : Kernel} {A : List Assumption}
    {L : Launch} {mem0 : Mem0} (hX : Consistent L K A mem0 X) {pc : Nat}
    (hget : X.get e = some ⟨pc,.mbInit m count⟩) :
    ∃ i r, (X.objects m)[i]? = some r ∧ r.id = .thread e ∧
      r.action = .init count ∧ RecordOk (stateBefore (X.objects m) i) r ∧
      ∀ j s, (X.objects m)[j]? = some s → s.id = .thread e → j = i :=
  init_record_of_consistent hX ⟨pc,hget⟩

/-- The successful initial response, with no arrival or transaction completion
invented. Its phase is zero and all expected arrivals remain pending. -/
def initReply (count : Nat) : Reply := ⟨some ⟨0,count,count,0,true⟩,none,none⟩

theorem init_record_success {before : Option State} {r : Record Ref}
    (hok : RecordOk before r) (ha : r.action = .init count)
    (hbefore : before = none) (hcount : validCount count) :
    r.fault = none ∧ r.reply = initReply count := by
  subst before
  have hp : perform none (.init count) = .ok (initReply count) := by
    simp [perform,initReply,hcount,pure,Except.pure,bind,Except.bind,throw,throwThe,
      MonadExceptOf.throw]
  unfold RecordOk at hok
  rw [ha,hp] at hok
  exact ⟨hok.2,hok.1⟩

/-- Source uniqueness of init records and dependencies for every non-init
record suffice to put the actual initializer at index zero. -/
theorem init_index_zero_of_unique_init (hX : Consistent L K A mem0 X)
    {i : Nat} {r : Record Ref} (hi : (X.objects m)[i]? = some r)
    (hid : r.id = .thread e)
    (hunique : ∀ (j : Nat) (s : Record Ref) (n : Nat), (X.objects m)[j]? = some s →
      s.action = .init n → s.id = .thread e)
    (hdeps : ∀ (j : Nat) (s : Record Ref), (X.objects m)[j]? = some s →
      (∀ n, s.action ≠ .init n) → ¬ Before (X.objects m) s.id (.thread e)) : i = 0 := by
  apply object_index_zero_of_not_before hX hi
  intro j s hs
  by_cases ha : ∃ n, s.action = .init n
  · obtain ⟨n,ha⟩ := ha
    exact .inl ((hunique j s n hs ha).trans hid.symm)
  · apply Or.inr
    rw [hid]
    exact hdeps j s hs (fun n hn => ha ⟨n,hn⟩)

/-- This finds the actual init record and proves its pre-state absent from
source uniqueness and dependencies, rather than supplying absence as a premise. -/
theorem init_record_first_of_unique_init (hX : Consistent L K A mem0 X)
    (hinit : X.MbInit e m count)
    (hunique : ∀ (j : Nat) (s : Record Ref) (n : Nat), (X.objects m)[j]? = some s →
      s.action = .init n → s.id = .thread e)
    (hdeps : ∀ (j : Nat) (s : Record Ref), (X.objects m)[j]? = some s →
      (∀ n, s.action ≠ .init n) → ¬ Before (X.objects m) s.id (.thread e)) :
    ∃ r, (X.objects m)[0]? = some r ∧ r.id = .thread e ∧
      r.action = .init count ∧ RecordOk none r := by
  obtain ⟨i,r,hi,hid,ha,hrecord,_⟩ := init_record_of_consistent hX hinit
  have hiz := init_index_zero_of_unique_init hX hi hid hunique hdeps
  subst i
  exact ⟨r,hi,hid,ha,by simpa only [stateBefore,↓reduceIte] using hrecord⟩

/-- The successful initial phase follows after proving first-record status;
checked histories by themselves supply no fault-freedom assumption. -/
theorem init_record_success_of_unique_init (hX : Consistent L K A mem0 X)
    (hinit : X.MbInit e m count) (hcount : validCount count)
    (hunique : ∀ (j : Nat) (s : Record Ref) (n : Nat), (X.objects m)[j]? = some s →
      s.action = .init n → s.id = .thread e)
    (hdeps : ∀ (j : Nat) (s : Record Ref), (X.objects m)[j]? = some s →
      (∀ n, s.action ≠ .init n) → ¬ Before (X.objects m) s.id (.thread e)) :
    ∃ r, (X.objects m)[0]? = some r ∧ r.id = .thread e ∧
      r.action = .init count ∧ r.fault = none ∧ r.reply = initReply count := by
  obtain ⟨r,hr,hid,ha,hrecord⟩ := init_record_first_of_unique_init hX hinit hunique hdeps
  obtain ⟨hf,hreply⟩ := init_record_success hrecord ha rfl hcount
  exact ⟨r,hr,hid,ha,hf,hreply⟩

/-- **An initialization that happens before the issue of an operation precedes the operation's
record in the object's history.** A thread record is ordered by causality with the object's order
at a pair with the initialization (`ObjectCoherent`); an asynchronous record by EXT-ASYNC-OBJECT
(`AsyncObjectOrdered`). -/
theorem object_not_before_of_baseCausality (hX : Consistent L K A mem0 X)
    {id : Ref} {init : EvId} (hinit : ∃ c, X.MbInit init m c)
    (hpub : baseCausality L X init id.issuer) :
    ¬ Before (X.objects m) id (.thread init) := by
  intro hbf
  obtain ⟨c, hc⟩ := hinit
  have hlife : MbarLifetimeRecord X m (.thread init) := ⟨init, rfl, .inl ⟨c, hc⟩⟩
  cases id with
  | thread u =>
    change baseCausality L X init u at hpub
    have h1 : WithObject L X (.mbar m) (.thread init, true) (.thread u, false) :=
      .inl (.inr (.inl ⟨rfl, rfl, init, u, rfl, rfl, hpub⟩))
    have h2 : WithObject L X (.mbar m) (.thread u, false) (.thread u, true) :=
      .inl (.inl (.inl ⟨rfl, rfl, rfl, present_of_len (baseCausality_events hpub).2⟩))
    have h3 : WithObject L X (.mbar m) (.thread u, true) (.thread init, true) :=
      .inr ⟨⟨rfl, rfl, hbf⟩, .inr (.inr (.inl hlife))⟩
    exact hX.object (.mbar m) _ (((Relation.TransGen.single h1).tail h2).tail h3)
  | async i p =>
    exact (hX.asyncObject m i p (.thread init) hbf).2 (.inl hlife)
      (.single (.inr (.inl ⟨rfl, rfl, init, i, rfl, rfl, hpub⟩)))

/-- **An initialization published by `fence.mbarrier_init` and a cluster barrier precedes the
operation's record in the object's history** (OBJ-MBAR-INIT-PUBLICATION, `Consistent.initFence`). -/
theorem object_not_before_of_init_fence (hX : Consistent L K A mem0 X)
    {id : Ref} {init : EvId} (hpub : InitFencePublished L X init id.issuer m) :
    ¬ Before (X.objects m) id (.thread init) := by
  obtain ⟨w, hs, hwb⟩ := hpub
  exact hX.initFence m init w id hs (.single (.inr (.inl ⟨rfl, rfl, w, id.issuer, rfl, rfl, hwb⟩)))

/-- A published initialization, by causality or by the init fence, precedes the operation's record
in the object's history. -/
theorem object_not_before_of_published (hX : Consistent L K A mem0 X)
    {id : Ref} {init : EvId} (hinit : ∃ c, X.MbInit init m c)
    (hpub : InitPublished L X init id.issuer m) :
    ¬ Before (X.objects m) id (.thread init) :=
  hpub.elim (object_not_before_of_baseCausality hX hinit) (object_not_before_of_init_fence hX)

end
end PTX
