-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tensor.TensorCompleteConsistent
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.MBarrier.MBarrierPhase
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Order.WaitingClosure
public import Lemmas.Order.Order
public import Lemmas.Order.CompletionFrame

@[expose] public section

section
/-! The notification stage records its real complete_tx in the selected object.
Origin, coverage and exact checked replies are preserved; no successful phase
or fault-free reply is postulated by the update definition. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

def Execution.recordTensorNotification (X : Execution) (i : EvId)
    (o : TensorCopy.Observation) (m : Loc) (r : Record Ref) : Execution :=
  (X.recordTensorEffects i o X.rf).appendObject m r

theorem tensor_notify_action_none {X : Execution} {i : EvId}
    (hn : (X.tensor i).any (fun old => old.effects.notified)=false) (m : Loc) :
    objectAction X X.async m (.async i (.notify .load))=none := by
  simp only [objectAction]
  split
  · cases ho : X.tensor i with
    | none => simp
    | some old =>
      have hn' : old.effects.notified=false := by simpa only [ho,Option.any_some] using hn
      simp [hn']
  · rfl

theorem no_tensor_notification_record {X : Execution} {i : EvId}
    (h : ObjectsOk X) (hn : (X.tensor i).any (fun old => old.effects.notified)=false)
    {m : Loc} {r : Record Ref} (hr : r∈X.objects m) : r.id≠.async i (.notify .load) := by
  intro he
  have ha := ((h m).2.1 r hr).1
  rw [he,tensor_notify_action_none hn m] at ha
  cases ha

/-- A fresh notification's checked reply extends the actual recorded state;
its operation identity freshness follows from the missing notification itself. -/
theorem tensorNotification_checked_snoc {X : Execution} {i : EvId}
    {m : Loc} {r : Record Ref} (h : ObjectsOk X)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load))
    (hr : RecordOk (stateBefore (X.objects m) (X.objects m).length) r) :
    CheckedLog (X.objects m++[r]) := by
  have hh := (h m).1.prefix (Nat.le_refl (X.objects m).length)
  rw [List.take_length] at hh
  apply CheckedLog.snoc hh (h m).1.1 ?_ hr
  intro hmem
  obtain ⟨q,hq,hqid⟩ := List.mem_map.mp hmem
  exact no_tensor_notification_record h hold hq (hqid.trans hid)

theorem recordTensorNotification_action_old {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m loc : Loc} {r : Record Ref} {id : Ref}
    (hne : id≠.async i (.notify .load)) :
    objectAction (X.recordTensorNotification i o m r)
      (X.recordTensorNotification i o m r).async loc id=
      objectAction X X.async loc id := by
  cases id with
  | thread j => rfl
  | async j part =>
    cases part <;> try rfl
    case notifyLoad =>
      have hj : j≠i := by intro he; subst j; exact hne rfl
      have hget : (X.recordTensorNotification i o m r).get=X.get := rfl
      have ht : (X.recordTensorNotification i o m r).tensor j=X.tensor j := by
        simp [Execution.recordTensorNotification,Execution.appendObject,
          Execution.recordTensorEffects,hj]
      simp only [objectAction,hget,ht]

theorem recordTensorNotification_action_new {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} {address : Nat}
    (hi : X.TensorIssue i address o.spec) (hn : o.effects.notified=true) (loc : Loc) :
    objectAction (X.recordTensorNotification i o m r)
      (X.recordTensorNotification i o m r).async loc (.async i (.notify .load))=
      if o.spec.mbar=loc then
        some (.completeTx (TensorTransfer.bytes o.spec.descriptor))
      else none := by
  obtain ⟨pc,he⟩ := hi
  have hget : (X.recordTensorNotification i o m r).get=X.get := rfl
  have ht : (X.recordTensorNotification i o m r).tensor i=some o := by
    simp [Execution.recordTensorNotification,Execution.appendObject,Execution.recordTensorEffects]
  simp only [objectAction,hget,he,ht,hn,and_true,bind,Option.bind]

/-- Every old record keeps its actual origin and every new notification is
represented on exactly the issue's own mbarrier. Checked errors are retained. -/
theorem recordTensorNotification_objects {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} {address : Nat}
    (h : ObjectsOk X) (hi : X.TensorIssue i address o.spec)
    (hmb : o.spec.mbar=m) (hn : o.effects.notified=true)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load))
    (ha : r.action=.completeTx (TensorTransfer.bytes o.spec.descriptor))
    (hc : CheckedLog (X.objects m++[r])) :
    ObjectsOk (X.recordTensorNotification i o m r) := by
  intro loc
  by_cases hm : loc=m
  · subst loc
    have hlog : (X.recordTensorNotification i o m r).objects m=X.objects m++[r] := by
      simp [Execution.recordTensorNotification,Execution.appendObject,Execution.recordTensorEffects]
    refine ⟨by rw [hlog]; exact hc,?_,?_⟩
    · intro q hq
      rw [hlog] at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨ha',hp⟩ := (h m).2.1 q hq
        exact ⟨(recordTensorNotification_action_old
          (no_tensor_notification_record h hold hq)).trans ha',hp⟩
      · have he := List.mem_singleton.mp hq
        subst q
        refine ⟨?_,?_⟩
        · rw [hid,recordTensorNotification_action_new hi hn,ite_eq_left hmb,ha]
        · intro p ok hp
          rw [ha] at hp
          cases hp
    · intro id action hact
      by_cases he : id=.async i (.notify .load)
      · exact ⟨r,by rw [hlog]; simp,hid.trans he.symm⟩
      · rw [recordTensorNotification_action_old he] at hact
        obtain ⟨q,hq,hqid⟩ := (h m).2.2 id action hact
        exact ⟨q,by rw [hlog]; exact List.mem_append_left _ hq,hqid⟩
  · have hlog : (X.recordTensorNotification i o m r).objects loc=X.objects loc := by
      simp [Execution.recordTensorNotification,Execution.appendObject,
        Execution.recordTensorEffects,hm]
    refine ⟨by rw [hlog]; exact (h loc).1,?_,?_⟩
    · intro q hq
      rw [hlog] at hq
      obtain ⟨ha',hp⟩ := (h loc).2.1 q hq
      exact ⟨(recordTensorNotification_action_old
        (no_tensor_notification_record h hold hq)).trans ha',hp⟩
    · intro id action hact
      by_cases he : id=.async i (.notify .load)
      · subst id
        rw [recordTensorNotification_action_new hi hn,
          ite_eq_right (by intro he; exact hm (he.symm.trans hmb))] at hact
        cases hact
      · rw [recordTensorNotification_action_old he] at hact
        obtain ⟨q,hq,hqid⟩ := (h loc).2.2 id action hact
        exact ⟨q,by rw [hlog]; exact hq,hqid⟩
/-- Appending an asynchronous tensor notification changes no ordinary hb
edge into an actual thread, and does not publish its issuer's generic stores. -/
theorem recordTensorNotification_baseCausality_iff {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} {e f : EvId}
    (hid : r.id=.async i (.notify .load)) :
    baseCausality L (X.recordTensorNotification i o m r) e f ↔ baseCausality L X e f := by
  unfold Execution.recordTensorNotification
  rw [appendObject_baseCausality_iff (fun w _ _ => by rw [hid]; simp)]
  exact recordTensorEffects_baseCausality_iff (fun _ _ => rfl)

theorem recordTensorNotification_observesMma_iff {X : Execution} {i mma waiter : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} {acq : Bool} {ws : MbarScope}
    (hid : r.id=.async i (.notify .load)) :
    AsyncObserved (X.recordTensorNotification i o m r) mma .mmaDone waiter acq ws ↔
      AsyncObserved X mma .mmaDone waiter acq ws := by
  unfold Execution.recordTensorNotification
  rw [appendObject_asyncObserved_iff (by rw [hid]; simp)]
  exact recordTensorEffects_observesMma_iff

theorem recordTensorNotification_semanticFrame {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref}
    (hid : r.id=.async i (.notify .load)) :
    TcMma.SemanticFrame L X (X.recordTensorNotification i o m r) :=
  ⟨fun _ => rfl,fun _ => rfl,rfl,rfl,fun _ _ => recordTensorNotification_baseCausality_iff hid,
    fun _ _ _ _ => recordTensorNotification_observesMma_iff hid,
    fun _ _ => by
      unfold Execution.recordTensorNotification
      rw [TcMma.appendObject_mbarExec_iff (by rw [hid]; simp)]
      rfl⟩

/-- A notification adds precisely its issue-derived checked object action. -/
theorem recordTensorNotification_tma {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} {address : Nat}
    (h : TmaOk X) (hi : X.TensorIssue i address o.spec)
    (hmb : o.spec.mbar=m) (hn : o.effects.notified=true)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load))
    (ha : r.action=.completeTx (TensorTransfer.bytes o.spec.descriptor))
    (hc : CheckedLog (X.objects m++[r])) :
    TmaOk (X.recordTensorNotification i o m r) :=
  ⟨h.1,h.2.1,recordTensorNotification_objects h.2.2.1 hi hmb hn hold hid ha hc,h.2.2.2⟩

/-- Recording the notification of a tensor load keeps the presence of every recorded object
update: no update of `X` is that notification. -/
theorem recordTensorNotification_present_record {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} (h : ObjectsOk X)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    {l : Loc} {q : Record Ref} (hq : q∈X.objects l) :
    (X.recordTensorNotification i o m r).RefPresent q.id ↔ X.RefPresent q.id := by
  have hne := no_tensor_notification_record h hold hq
  rcases record_id_cases h hq with ⟨t, he⟩ | ⟨j, he⟩ | ⟨j, he⟩ | ⟨j, c, he⟩ | ⟨j, he⟩ |
    ⟨j, rk, he⟩ <;> rw [he] at hne ⊢
  case inr.inr.inl =>
    have hj : j≠i := fun hj => hne (by rw [hj])
    simp only [Execution.RefPresent, Execution.AsyncPresent, Execution.recordTensorNotification,
      Execution.appendObject, Execution.recordTensorEffects, hj, ↓reduceIte]
  all_goals exact Iff.rfl

/-- Recording the notification of a tensor load changes no need: the new record is observed by
no wait, and the presence of every recorded update is old. -/
theorem recordTensorNotification_needs {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} (h : ObjectsOk X)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load)) (e : EvId) :
    Needs L (X.recordTensorNotification i o m r) e = Needs L X e := by
  refine (appendObject_needs (X := X.recordTensorEffects i o X.rf)
    (fun l q hq he => no_tensor_notification_record h hold hq (he.trans hid))
    (fun e he => by rw [hid] at he; cases he) e).trans ?_
  refine needs_congr (X := X) (Y := X.recordTensorEffects i o X.rf) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e l => pollNeeds_congr (X := X) (Y := X.recordTensorEffects i o X.rf) (fun _ => rfl)
      (fun l q hq w => and_congr ?_ Iff.rfl) e l) e
  exact recordTensorNotification_present_record (m := m) (r := r) h hold hq

/-- Readiness survives recording the notification. -/
theorem recordTensorNotification_ready {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref} (h : ObjectsOk X)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load)) (hready : ∀ e, Returned X e → Ready L X e) :
    ∀ e, Returned (X.recordTensorNotification i o m r) e →
      Ready L (X.recordTensorNotification i o m r) e := by
  refine ready_congr (X := X) (L := L) (recordTensorNotification_needs h hold hid) (fun e h => h)
    (fun j fills x hn' hf hx => ?_) hready
  rcases needs_node_cases hn' hf with ⟨t, he⟩ | ⟨a, k, p, he, hp⟩ | ⟨l, q, hq, he⟩
  · subst he; exact hx
  · subst he
    rcases groupWaitStages_cases X a k hp with rfl | rfl | rfl | rfl <;> exact hx
  · subst he; exact (recordTensorNotification_present_record h hold hq).mpr hx

/-- Record the real tensor notification while preserving all static source and
resource constraints. The new byte/phase visibility is the remaining dynamic
obligation of the concrete pipeline proof. -/
theorem consistent_recordTensorNotification {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {m : Loc} {r : Record Ref} {address : Nat}
    (hX : Consistent L K A mem0 X) (hi : X.TensorIssue i address o.spec)
    (hcopy : TensorCopy.CopyOk o.spec o.effects)
    (hrouting : TensorCopy.RoutingOk L (i.1/L.block) o.spec)
    (hv : TensorDescriptor.Valid o.spec.descriptor)
    (hmb : o.spec.mbar=m) (hn : o.effects.notified=true)
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hid : r.id=.async i (.notify .load))
    (haction : r.action=.completeTx (TensorTransfer.bytes o.spec.descriptor))
    (hchecked : CheckedLog (X.objects m++[r]))
    (hr : RfWf mem0 (X.recordTensorNotification i o m r))
    (ha : OrderOk L K A (X.recordTensorNotification i o m r))
    (hf : NoFuture L (X.recordTensorNotification i o m r))
    (hh : Hidden L (X.recordTensorNotification i o m r))
    (hasm : ∀a∈A,a.wf L mem0 (X.recordTensorNotification i o m r)) :
    Consistent L K A mem0 (X.recordTensorNotification i o m r) where
  thr := hX.thr
  outside := hX.outside
  rf := hr
  ctaBar := hX.ctaBar
  cluster := hX.cluster
  dependency := ⟨recordTensorNotification_ready hX.tma.2.2.1 hold hid hX.dependency.ready,
    ha.depAcyclic⟩
  shfl := hX.shfl
  vote := hX.vote
  warpValue := hX.warpValue
  matrix := hX.matrix
  elect := hX.elect
  warpBar := hX.warpBar
  observation := ha.observation
  object := ha.object
  asyncObject := ha.asyncObject
  initFence := ha.initFence
  noFuture := hf
  hidden := hh
  tma := recordTensorNotification_tma hX.tma hi hmb hn hold hid haction hchecked
  clc := hX.clc
  tensor := recordTensorEffects_tensor (rf := X.rf) hX.tensor ⟨address,hi⟩ hcopy hrouting hv
  store := hX.store
  reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩
  atomic := atomicOk_congr (X := X) (Y := X.recordTensorNotification i o m r)
    (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => rmwStrong_congr rfl rfl)
    (fun p k => by cases p <;> rfl) hX.atomic
  fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
    hX.fenceSc.causal e f hs ((recordTensorNotification_baseCausality_iff hid).mp h)⟩
  tmemPair := hX.tmemPair
  tmemPairResult := hX.tmemPairResult
  tcCommit := hX.tcCommit
  tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
  mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
  tcRead := (recordTensorNotification_semanticFrame hid).readOk.mpr hX.tcRead
  asm := hasm

/-- Adding the notification retains every prior effect, read source and object
record. The checked transition itself is established separately above. -/
theorem Execution.le_recordTensorNotification {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref}
    (hobs : ∀old,X.tensor i=some old → old.Extends o) :
    X.le (X.recordTensorNotification i o m r) :=
  Execution.le_trans (Execution.le_recordTensorEffects hobs (fun _ _ _ => rfl))
    (Execution.le_appendObject _ m r)

/-- The terminal notification is an independent counted async effect. -/
theorem recordTensorNotification_size {X : Execution} {L : Launch} {i : EvId}
    {o : TensorCopy.Observation} {m : Loc} {r : Record Ref}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length)
    (hs : ((X.tensor i).map (fun old => old.effects.size)).getD 0<o.effects.size) :
    X.size L<(X.recordTensorNotification i o m r).size L :=
  recordTensorEffects_size_of_measure (rf := X.rf) hg hi hs
namespace TensorCopy

/-- Notify a bytewise-complete observation, retaining all recorded byte data. -/
def Observation.notifiedObservation (o : Observation) : Observation :=
  ⟨o.spec,{o.effects with notified := true}⟩

theorem notifiedObservation_copyOk {o : Observation}
    (h : CopyOk o.spec o.effects)
    (hw : ∀slot,∃value,o.effects.write slot=some value) :
    CopyOk o.notifiedObservation.spec o.notifiedObservation.effects :=
  ⟨h.reads,h.writes,fun _ => hw⟩

theorem notifiedObservation_extends (o : Observation) : o.Extends o.notifiedObservation :=
  ⟨rfl,fun _ _ h => h,fun _ _ h => h,fun _ => rfl⟩

theorem notifiedObservation_size {o : Observation} (hn : o.effects.notified=false) :
    o.notifiedObservation.effects.size=o.effects.size+1 := by
  simp [Observation.notifiedObservation,Effects.size,Effects.readSlots,Effects.writeSlots,hn]
  rfl

end TensorCopy

/-- Once all independent writes exist, setting the notification adds exactly
one counted stage. No extra size assumption is needed from the pipeline. -/
theorem notifiedObservation_counted {X : Execution} {L : Launch} {i : EvId}
    {o : TensorCopy.Observation} {r : Record Ref}
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) :
    X.size L<(X.recordTensorNotification i o.notifiedObservation o.spec.mbar r).size L := by
  apply recordTensorNotification_size hg hi
  rw [ho]
  change o.effects.size<o.notifiedObservation.effects.size
  rw [TensorCopy.notifiedObservation_size hn]
  omega

end
end PTX
end

section
/-! A bytewise-complete tensor load's final notification adds no new memory
access, and an appended asynchronous record cannot publish to an old wait. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {m : Loc} {r : Record Ref}
local notation "Y" => X.recordTensorNotification i o.notifiedObservation m r

theorem tensorNotifyFrame_reads (ho : X.tensor i=some o) :
    ∀e a bs,(Y).MemReads e a bs ↔ X.MemReads e a bs := by
  intro e a bs
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemReads,Execution.recordTensorNotification,
          Execution.appendObject,Execution.recordTensorEffects,↓reduceIte,ho]
        simp only [Option.some.injEq,exists_and_left,exists_eq_left']
        try rfl
      · simp only [Execution.MemReads,Execution.recordTensorNotification,
          Execution.appendObject,Execution.recordTensorEffects,ite_eq_right hj]
        try rfl

theorem tensorNotifyFrame_writes (ho : X.tensor i=some o) :
    ∀e a bs,(Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  intro e a bs
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemWrites,Execution.recordTensorNotification,
          Execution.appendObject,Execution.recordTensorEffects,↓reduceIte,ho]
        simp only [Option.some.injEq,exists_and_left,exists_eq_left']
        try rfl
      · simp only [Execution.MemWrites,Execution.recordTensorNotification,
          Execution.appendObject,Execution.recordTensorEffects,ite_eq_right hj]
        try rfl

theorem tensorNotifyFrame_covers (j : EvId) (p : Part) (l : Loc) :
    AsyncCovers Y j p l ↔ AsyncCovers X j p l := by
  cases p <;> rfl

theorem tensorNotifyFrame_present (ho : X.tensor i=some o) {j : EvId} {p : Part}
    (hne : (j,p)≠(i,(.notify .load))) : (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  case readLoad x y k =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorNotification,
        Execution.appendObject,Execution.recordTensorEffects,↓reduceIte,ho]
      simp only [Option.some.injEq,exists_eq_left']
      try rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorNotification,
        Execution.appendObject,Execution.recordTensorEffects,ite_eq_right hj]
  case writeLoad x y k =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorNotification,
        Execution.appendObject,Execution.recordTensorEffects,↓reduceIte,ho]
      simp only [Option.some.injEq,exists_and_left,exists_eq_left']
      try rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorNotification,
        Execution.appendObject,Execution.recordTensorEffects,ite_eq_right hj]
  case notifyLoad =>
    have hj : j≠i := by intro h; subst j; exact hne rfl
    simp only [Execution.AsyncPresent,Execution.recordTensorNotification,
      Execution.appendObject,Execution.recordTensorEffects,ite_eq_right hj]
theorem tensorNotifyFrame_observed (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) (copy waiter : EvId) (p : Part) (acq : Bool)
    (ws : MbarScope) :
    AsyncObserved Y copy p waiter acq ws ↔ AsyncObserved X copy p waiter acq ws := by
  have hneq : r.id ≠ .thread waiter := by rw [hid]; simp
  unfold Execution.recordTensorNotification
  rw [appendObject_asyncObserved_iff hneq]
  have hnone (loc : Loc) :
      ¬UpdateBeforeWait (X.objects loc) (.async i (.notify .load)) (.thread waiter) := by
    rintro ⟨a,_,rec,_,_,hget,hid',_⟩
    exact no_tensor_notification_record hobjects (by simp [ho,hn])
      (List.mem_of_getElem? hget) hid'
  cases p <;> try rfl
  all_goals
    by_cases hi : copy=i
    · subst copy
      constructor
      · rintro ⟨n,loc,⟨rfl,-⟩,-,hu⟩
        exact (hnone loc hu).elim
      · rintro ⟨n,loc,⟨rfl,-⟩,-,hu⟩
        exact (hnone loc hu).elim
    · have ht : (X.recordTensorEffects i o.notifiedObservation X.rf).tensor copy=X.tensor copy := by
        simp [Execution.recordTensorEffects,hi]
      simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,ht]
      rfl

/-- The stages that a group wait waits for are no tensor-load stages, so their presence is
unchanged. -/
theorem tensorNotifyFrame_groupPresent (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages Y j k, (Y).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl

theorem tensorNotifyFrame_finished (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) (j : EvId) (p : Part) (waiter : EvId) :
    AsyncFinished L Y j p waiter ↔ AsyncFinished L X j p waiter :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
      tensorNotifyFrame_groupPresent j k)
    (exists_congr fun ws =>
      and_congr_left' (tensorNotifyFrame_observed hobjects ho hn hid j waiter _ true ws))

theorem tensorNotifyFrame_onlyFinished (j : EvId) (p : Part) (waiter : EvId) :
    AsyncOnlyFinished Y j p waiter ↔ AsyncOnlyFinished X j p waiter :=
  and_congr_right fun _ => and_congr_right fun _ => tensorNotifyFrame_groupPresent j _

theorem tensorNotifyFrame_chain (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) (l : Loc) (a b : EvId × Part) :
    AsyncChain L Y l a b ↔ AsyncChain L X l a b := by
  have hd (a b : EvId × Part) : AsyncBefore L Y l a b ↔ AsyncBefore L X l a b :=
    AsyncBefore.congr (fun j p => tensorNotifyFrame_covers j p l)
      (tensorNotifyFrame_finished hobjects ho hn hid) tensorNotifyFrame_onlyFinished
      (fun _ _ _ _ => recordTensorNotification_baseCausality_iff hid) (fun _ _ _ _ => Iff.rfl)
  apply AsyncChain.congr_on_edges hd
  intro a b hedge
  apply tensorNotifyFrame_present ho
  intro heq
  change a=(i,(.notify .load)) at heq
  rw [heq] at hedge
  obtain ⟨acc,w,hi,_⟩ := hedge.1
  exact hi.2

theorem tensorNotifyFrame_modelCausality (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) (l : Loc) (e f : Ref) :
    modelCausality L Y l e f ↔ modelCausality L X l e f := by
  cases e with
  | thread e =>
    cases f with
    | thread f => exact or_congr (recordTensorNotification_baseCausality_iff hid) Iff.rfl
    | async j p =>
      have hc := tensorNotifyFrame_covers (X := X) (i := i) (o := o) (m := m) (r := r) j p l
      simp only [modelCausality,hc]
      unfold ProxyBefore
      simp only [recordTensorNotification_baseCausality_iff hid]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hc := tensorNotifyFrame_covers (X := X) (i := i) (o := o) (m := m) (r := r) j p l
      have hp : ∀ e f, ProxyBefore L Y e f l ↔ ProxyBefore L X e f l := by
        intro e f
        unfold ProxyBefore
        simp only [recordTensorNotification_baseCausality_iff hid]
        rfl
      have hcb (w : EvId) :
          ObservedCompletionBefore L Y l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr rfl rfl
          (recordTensorNotification_baseCausality_iff hid) (hp w f)
      simp only [modelCausality,hc,tensorNotifyFrame_finished hobjects ho hn hid,hcb]
    | async k q =>
      exact and_congr_right fun _ => tensorNotifyFrame_chain hobjects ho hn hid l (j,p) (k,q)

theorem tensorNotifyFrame_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o) : RfWf mem0 Y := by
  intro e a bs he
  obtain ⟨hlen,hr⟩ := hX.rf e a bs ((tensorNotifyFrame_reads ho e a bs).mp he)
  refine ⟨hlen,?_⟩
  intro k hk
  have hs := hr k hk
  change match X.rf e k with
    | none => _
    | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hs ⊢; exact hs
  | some w =>
    rw [hsrc] at hs
    obtain ⟨dst,bytes,hw,hcover,hbyte⟩ := hs
    exact ⟨dst,bytes,(tensorNotifyFrame_writes ho w dst bytes).mpr hw,hcover,hbyte⟩

private theorem tensorNotifyFrame_byteCausality (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false) (hid : r.id=.async i (.notify .load))
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (tensorNotifyFrame_modelCausality hobjects ho hn hid l e f).mp)
    (fun h => (recordTensorNotification_observesMma_iff hid).mp h)

theorem tensorNotifyFrame_noFuture {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hn : o.effects.notified=false) (hid : r.id=.async i (.notify .load)) : NoFuture L Y :=
  hX.noFuture.of_frame (fun e a bs => (tensorNotifyFrame_reads ho e a bs).mp) rfl
    (fun _ _ _ => tensorNotifyFrame_byteCausality hX.tma.2.2.1 ho hn hid)

theorem tensorNotifyFrame_hidden {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hn : o.effects.notified=false) (hid : r.id=.async i (.notify .load)) : Hidden L Y :=
  hX.hidden.of_frame (fun e a bs => (tensorNotifyFrame_reads ho e a bs).mp)
    (fun e a bs => (tensorNotifyFrame_writes ho e a bs).mp) rfl
    (fun _ _ _ => tensorNotifyFrame_byteCausality hX.tma.2.2.1 ho hn hid)

theorem tensorNotifyFrame_refPresent (ho : X.tensor i=some o) {e : Ref}
    (hne : e≠.async i (.notify .load)) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    exact tensorNotifyFrame_present ho
      (fun he => hne (congrArg (fun pair => Ref.async pair.1 pair.2) he))

theorem tensorNotifyFrame_no_before (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false) (loc : Loc) (f : Ref) :
    ¬Before ((Y).objects loc) (.async i (.notify .load)) f := by
  rintro ⟨a,b,ra,rb,ha,hid,hb,_,hab⟩
  by_cases hm : loc=m
  · subst loc
    have hb' : (X.objects m++[r])[b]?=some rb := by
      simpa only [Execution.recordTensorNotification,Execution.appendObject,
        Execution.recordTensorEffects,↓reduceIte] using hb
    have hbl := (List.getElem?_eq_some_iff.mp hb').1
    have hao : a<(X.objects m).length := by
      simp only [List.length_append,List.length_singleton] at hbl
      omega
    have ha' : (X.objects m)[a]?=some ra := by
      simpa only [Execution.recordTensorNotification,Execution.appendObject,
        Execution.recordTensorEffects,↓reduceIte,List.getElem?_append_left hao] using ha
    exact no_tensor_notification_record hobjects (by simp [ho,hn])
      (List.mem_of_getElem? ha') hid
  · have ha' : (X.objects loc)[a]?=some ra := by
      simpa only [Execution.recordTensorNotification,Execution.appendObject,
        Execution.recordTensorEffects,ite_eq_right hm] using ha
    exact no_tensor_notification_record hobjects (by simp [ho,hn])
      (List.mem_of_getElem? ha') hid

/-- The new notification fills no need: it is no stage of a group wait and no recorded update of
`X`. -/
theorem tensorNotifyFrame_not_witness (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) (w : EvId) :
    ¬ Witness L Y (.async i (.notify .load)) w := by
  refine not_witness_of_needRef (recordTensorNotification_needs hobjects (by simp [ho,hn]) hid w) ?_
  rintro (⟨t, h⟩ | ⟨a, k, q, h, hq⟩ | ⟨l, q, hq, h⟩)
  · cases h
  · cases h
    rcases groupWaitStages_cases X _ k hq with h | h | h | h <;> cases h
  · exact no_tensor_notification_record hobjects (by simp [ho,hn]) hq h.symm

theorem tensorNotifyFrame_waits_from_notify (hobjects : ObjectsOk X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) {b : Bool} {v : Ref × Bool}
    (h : Waits L Y (.async i (.notify .load),b) v) :
    v.1=.async i (.notify .load) ∧ b=false ∧ v.2=true := by
  rcases h with ⟨he,hb,hb',_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨_,_,ha⟩ | ⟨_,_,loc,ho'⟩ | ⟨j,k,he,_⟩ | ⟨_,_,w,-,hw⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,hi⟩
  · exact ⟨he.symm,hb,hb'⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · exfalso
    rcases ha with ⟨-,h0,-⟩ | ⟨-,-,ha⟩
    · simp_all
    · cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p => rw [hv] at ha; cases p <;> exact ha
  · exact (tensorNotifyFrame_no_before hobjects ho hn loc v.1 ho').elim
  · cases he
  · exact (tensorNotifyFrame_not_witness hobjects ho hn hid w hw).elim
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨_,_,k,q,he,_⟩ := hi
    cases he

/-- The appended notification waits on nothing and has no successor in its object;
outside it every order relation is old. -/
theorem tensorNotifyFrame_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hid : r.id=.async i (.notify .load)) :
    SinkFrame L K A X Y (CompletionNodes L Y (· = .async i (.notify .load))) := by
  have hobjects : ObjectsOk X := hX.tma.2.2.1
  have hnot : ∀ {w : Ref}, ¬w=.async i (.notify .load) → r.id≠w := fun hw he =>
    hw (he.symm.trans hid)
  have hth : ∀ e, r.id ≠ .thread e := fun e h => by rw [hid] at h; cases h
  have hpres : ∀ {e : Ref}, e ≠ .async i (.notify .load) → (Y).RefPresent e → X.RefPresent e :=
    fun he h => (tensorNotifyFrame_refPresent ho he).mp h
  have hold : ∀ {u : Ref × Bool}, ¬ CompletionNodes L Y (· = .async i (.notify .load)) u →
      u.1 ≠ .async i (.notify .load) := fun hu he => hu (.inl he)
  have hobject : ∀ o' (u v : Ref × Bool), v.1 ≠ .async i (.notify .load) →
      ObjectOrder L Y o' u v → ObjectOrder L X o' u v :=
    fun o' u v hv h => (appendObject_objectOrder_iff
      (X := X.recordTensorEffects i o.notifiedObservation X.rf) (hnot hv)).mp h
  have hneeds := recordTensorNotification_needs (L := L) (o := o.notifiedObservation) (m := m)
    hobjects (by simp [ho,hn]) hid
  refine sinkFrame_completion (· = .async i (.notify .load)) (fun _ h => by cases h)
    (fun u v hu h => ?_)
    (fun w x hx hw => (tensorNotifyFrame_not_witness hobjects ho hn hid w (hx ▸ hw)).elim)
    (fun u v hu hv hc => ?_) (fun x w hx hw h => ?_)
    (fun o' u v _ hv h => hobject o' u v (hold hv) h) (fun o' u v _ hv h => ?_)
    (fun u v hu hv hc => ?_) (fun m' j p y hb => ?_) (fun m' j p y _ _ h => ?_) hX.initFence
    (fun _ _ _ h => h) (fun m' y init h => ?_) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    change e = _ at hu
    subst hu
    exact .inl (tensorNotifyFrame_waits_from_notify hobjects ho hn hid h)
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, h7, h8⟩
    · exact .single (.inl (StageOrder.transfer (X := X)
        («Y» := X.recordTensorNotification i o.notifiedObservation m r)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4,
        (recordTensorNotification_baseCausality_iff hid).mp hc⟩))
    · exact .single (.inr (.inr ⟨h1, h2, k, h3, c, p, w, ws, h5, h6,
        (tensorNotifyFrame_observed hobjects ho hn hid c w p true ws).mp h7, h8⟩))
  · have hx' : x ≠ .async i (.notify .load) := hold hx
    have hw' : w ≠ .async i (.notify .load) := hold hw
    rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · have h' := (appendObject_mbarObserved_iff
        (X := X.recordTensorEffects i o.notifiedObservation X.rf) (hnot hx') (hnot hw')).mp hm
      exact .inl ⟨⟨hpres hx' h'.1, h'.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres hx' h3, h4, h5⟩
  · cases o' with
    | mbar m' => exact ⟨hobject _ u v (hold hv) h.1, h.2⟩
    | ctaBar c id => exact hobject (.ctaBar c id) u v (hold hv) h
    | cluster c => exact hobject (.cluster c) u v (hold hv) h
    | tmem c => exact hobject (.tmem c) u v (hold hv) h
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | ⟨h1, h2, j, hj, fills, hn', hx, hf⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X)
        («Y» := X.recordTensorNotification i o.notifiedObservation m r)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X)
        («Y» := X.recordTensorNotification i o.notifiedObservation m r) (fun _ => rfl)
        (hpres (hold hv)) hc)))
    · rw [hneeds] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))
  · by_cases hy : r.id = y
    · rintro ⟨k, rfl, -⟩
      exact hth k hy
    · have hb' := (appendObject_objectOrder_iff
        (X := X.recordTensorEffects i o.notifiedObservation X.rf) (L := L)
        (o := .mbar m') (u := (.async j p, true)) (v := (y, true)) hy).mp ⟨rfl, rfl, hb⟩
      exact (hX.asyncObject m' j p y hb'.2.2).1
  · rcases h with h | ⟨k, ws, rfl, hw⟩
    · exact .inl h
    · exact .inr ⟨k, ws, rfl, (appendObject_waitObserves_iff (hth k)).mp hw⟩
  · have hb' := (appendObject_objectOrder_iff
      (X := X.recordTensorEffects i o.notifiedObservation X.rf) (L := L)
      (o := .mbar m') (u := (y, true)) (v := (.thread init, true)) (hth init)).mp ⟨rfl, rfl, h⟩
    exact hb'.2.2

end
end PTX
end
