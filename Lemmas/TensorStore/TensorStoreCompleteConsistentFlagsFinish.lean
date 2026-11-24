-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.TensorStore.TensorStoreSize
public import Lemmas.Tcgen05.TcReadSemanticFrame
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Execution.EffectFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistent
public import Lemmas.Snoc.Snoc
public import Lemmas.Order.CompletionFrame

@[expose] public section

section
/-! Completion flags record already available tensor-store bytes. They neither
choose new byte values nor infer completion merely from a commit instruction. -/
namespace PTX
open AsyncCopy
noncomputable section

def TensorStore.Observation.doneFlags (o : TensorStore.Observation) (reads full : Bool) :
    TensorStore.Observation :=
  {o with effects:={o.effects with readsDone:=reads,fullDone:=full}}

def Execution.storeDoneFlags (X : Execution) (i : EvId) (o : TensorStore.Observation)
    (reads full : Bool) : Execution :=
  {X with tensorStores:=fun j => if j=i then some (o.doneFlags reads full) else X.tensorStores j}

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {reads full : Bool}

 theorem storeDoneFlags_memReads (ho : X.tensorStores i=some o)
    {e : Ref} {a : Acc} {bs : List (Option Byte)} :
    (X.storeDoneFlags i o reads full).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try exact Iff.rfl
    case readStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemReads,Execution.storeDoneFlags,ho,TensorStore.Observation.doneFlags,
          TensorStore.readByte,Execution.TensorStoreIssue,Execution.get]
      · simp only [Execution.MemReads,Execution.storeDoneFlags,ite_eq_right hj]
        rfl
    case oldStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemReads,Execution.storeDoneFlags,ho,TensorStore.Observation.doneFlags,
          TensorStore.oldByte,Execution.TensorStoreIssue,Execution.get]
      · simp only [Execution.MemReads,Execution.storeDoneFlags,ite_eq_right hj]
        rfl

 theorem storeDoneFlags_memWrites (ho : X.tensorStores i=some o)
    {e : Ref} {a : Acc} {bs : List Byte} :
    (X.storeDoneFlags i o reads full).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try exact Iff.rfl
    case writeStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemWrites,Execution.storeDoneFlags,ho,TensorStore.Observation.doneFlags,
          TensorStore.writeByte,Execution.TensorStoreIssue,Execution.get]
      · simp only [Execution.MemWrites,Execution.storeDoneFlags,ite_eq_right hj]
        rfl

 theorem storeDoneFlags_extends (o : TensorStore.Observation) (reads full : Bool)
    (hr : o.effects.readsDone=true → reads=true)
    (hf : o.effects.fullDone=true → full=true) :
    o.Extends (o.doneFlags reads full) :=
  ⟨rfl,fun _ _ h => h,fun _ _ h => h,hr,hf,fun _ => rfl,fun _ _ h => h⟩

 theorem storeDoneFlags_le (ho : X.tensorStores i=some o)
    (hr : o.effects.readsDone=true → reads=true)
    (hf : o.effects.fullDone=true → full=true) :
    X.le (X.storeDoneFlags i o reads full) := by
  have h := Execution.le_refl X
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,?_,
    h.2.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  intro j obs hj
  by_cases he : j=i
  · subst j
    have heq : obs=o := Option.some.inj (hj.symm.trans ho)
    subst obs
    exact ⟨o.doneFlags reads full,by simp [Execution.storeDoneFlags],
      storeDoneFlags_extends o reads full hr hf⟩
  · exact ⟨obs,by simpa [Execution.storeDoneFlags,he] using hj,
      TensorStore.Observation.extends_refl _⟩

end
end PTX
end

section
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {reads full : Bool}

 theorem storeDoneFlags_present_memory (ho : X.tensorStores i=some o)
    {j : EvId} {p : Part} (hreads : p≠.readsDone) (hfull : p≠.fullDone) :
    (X.storeDoneFlags i o reads full).AsyncPresent j p ↔ X.AsyncPresent j p := by
  by_cases hj : j=i
  · subst j
    cases p <;> try exact Iff.rfl
    all_goals first
      | exact (hreads rfl).elim
      | exact (hfull rfl).elim
      | (simp [Execution.AsyncPresent,Execution.storeDoneFlags,ho,
          TensorStore.Observation.doneFlags,TensorStore.readByte,TensorStore.writeByte,
          TensorStore.oldByte])
  · cases p <;> simp only [Execution.AsyncPresent,Execution.storeDoneFlags,ite_eq_right hj]
    all_goals rfl

/-- No object records a completion flag of a tensor store. -/
theorem record_not_storeDone (hobj : ObjectsOk X) {m : Loc} {r : MBarrier.Record Ref}
    (hr : r ∈ X.objects m) {j : EvId} {p : Part} (hp : p = .readsDone ∨ p = .fullDone) :
    r.id ≠ .async j p := by
  intro hid
  have hm := ((hobj m).2.1 r hr).1
  rcases hp with rfl | rfl <;> simp [objectAction,hid] at hm

/-- The presence of a recorded object update is unchanged by the completion flags. -/
theorem storeDoneFlags_present_record (hobj : ObjectsOk X) (ho : X.tensorStores i=some o)
    {m : Loc} {r : MBarrier.Record Ref} (hr : r ∈ X.objects m) :
    (X.storeDoneFlags i o reads full).RefPresent r.id ↔ X.RefPresent r.id := by
  generalize hid : r.id = id
  cases id with
  | thread j => exact Iff.rfl
  | async j p =>
    exact storeDoneFlags_present_memory ho
      (fun h => record_not_storeDone hobj hr (.inl h) hid)
      (fun h => record_not_storeDone hobj hr (.inr h) hid)

/-- The needs of every event are unchanged by the completion flags. -/
theorem storeDoneFlags_needs (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) (e : EvId) :
    Needs L (X.storeDoneFlags i o reads full) e = Needs L X e :=
  needs_congr (X := X) (Y := X.storeDoneFlags i o reads full) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := X.storeDoneFlags i o reads full)
      (fun _ => rfl)
      (fun _ _ hr _ => and_congr (storeDoneFlags_present_record hobj ho hr) Iff.rfl) e m) e

/-- A completion observed in the extension is observed in `X`, or by a group wait that has not
returned in `X`. -/
theorem storeDoneFlags_finished (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) {j w : EvId} {p : Part}
    (h : AsyncFinished L (X.storeDoneFlags i o reads full) j p w) :
    AsyncFinished L X j p w ∨ (GroupWaitEvent X w ∧ ¬ Returned X w) :=
  asyncFinished_completion hready (storeDoneFlags_needs hobj ho) (fun _ _ _ h => h)
    (fun _ _ => rfl) (fun _ _ _ _ h => h) h

theorem storeDoneFlags_onlyFinished (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) {j w : EvId} {p : Part}
    (h : AsyncOnlyFinished (X.storeDoneFlags i o reads full) j p w) :
    AsyncOnlyFinished X j p w ∨ (GroupWaitEvent X w ∧ ¬ Returned X w) :=
  asyncOnlyFinished_completion hready (storeDoneFlags_needs hobj ho) (fun _ _ _ h => h)
    (fun _ _ => rfl) h

theorem storeDoneFlags_before (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) {l : Loc} {a b : EvId × Part}
    (h : AsyncBefore L (X.storeDoneFlags i o reads full) l a b) : AsyncBefore L X l a b := by
  obtain ⟨hca, hcb, ⟨w, hf, hb⟩ | ⟨w, hf, hp⟩⟩ := h
  · rcases storeDoneFlags_finished hready hobj ho hf with hf | ⟨hw, hr⟩
    · exact ⟨hca, hcb, .inl ⟨w, hf, hb⟩⟩
    · exact (groupWait_last_not_baseCausality (X := X) hw (hw.last hr) hb).elim
  · rcases storeDoneFlags_onlyFinished hready hobj ho hf with hf | ⟨hw, hr⟩
    · exact ⟨hca, hcb, .inr ⟨w, hf, hp⟩⟩
    · exact (groupWait_last_not_po (hw.last hr) hp).elim

/-- The model causality of the extension is that of `X`: a wait that observes the completion only
in the extension has not returned, so nothing follows it. -/
theorem storeDoneFlags_modelCausality (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) {l : Loc} {e f : Ref}
    (h : modelCausality L (X.storeDoneFlags i o reads full) l e f) : modelCausality L X l e f := by
  cases e <;> cases f
  · exact h
  · exact h
  · obtain ⟨hc, w, hf, hb⟩ := h
    rcases storeDoneFlags_finished hready hobj ho hf with hf | ⟨hw, hr⟩
    · exact ⟨hc, w, hf, hb⟩
    · rcases hb with hb | hb
      · exact (groupWait_last_not_completionBefore (X := X) hw (hw.last hr) hb).elim
      · exact (groupWait_last_not_baseCausality (X := X) hw (hw.last hr)
          (TcReadReuseBefore.base L hb)).elim
  · refine ⟨h.1, h.2.map (fun h => storeDoneFlags_before hready hobj ho h) ?_⟩
    intro a b hp hedge
    refine (storeDoneFlags_present_memory ho ?_ ?_).mp hp
    all_goals
      intro hp
      rcases hedge.1 with ⟨footprint,write,hi,_⟩
      rw [hp] at hi
      cases hi.2

 theorem storeDoneFlags_rf {mem0 : Mem0} (hX : RfWf mem0 X) (ho : X.tensorStores i=some o) :
    RfWf mem0 (X.storeDoneFlags i o reads full) := by
  unfold RfWf
  simp only [storeDoneFlags_memReads ho,storeDoneFlags_memWrites ho]
  exact hX

 theorem storeDoneFlags_noFuture (hX : NoFuture L X) (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) :
    NoFuture L (X.storeDoneFlags i o reads full) :=
  NoFuture.of_frame hX (fun _ _ _ h => (storeDoneFlags_memReads ho).mp h) rfl
    (fun _ _ _ => ByteCausality.of_same_context (L := L) (X := X)
      (Y := X.storeDoneFlags i o reads full) rfl rfl
      (storeDoneFlags_modelCausality hready hobj ho) (fun h => h))

 theorem storeDoneFlags_hidden (hX : Hidden L X) (hready : ∀ e, Returned X e → Ready L X e)
    (hobj : ObjectsOk X) (ho : X.tensorStores i=some o) :
    Hidden L (X.storeDoneFlags i o reads full) :=
  Hidden.of_frame hX (fun _ _ _ h => (storeDoneFlags_memReads ho).mp h)
    (fun _ _ _ h => (storeDoneFlags_memWrites ho).mp h) rfl
    (fun _ _ _ => ByteCausality.of_same_context (L := L) (X := X)
      (Y := X.storeDoneFlags i o reads full) rfl rfl
      (storeDoneFlags_modelCausality hready hobj ho) (fun h => h))

end
end PTX
end

section
namespace PTX
open AsyncCopy MBarrier
noncomputable section

def storeDonePart (fullStage : Bool) : Part :=
  if fullStage then .fullDone else .readsDone

def Execution.finishStoreFlag (X : Execution) (i : EvId) (o : TensorStore.Observation)
    (fullStage : Bool) : Execution :=
  X.storeDoneFlags i o (if fullStage then o.effects.readsDone else true)
    (if fullStage then true else o.effects.fullDone)

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation} {stage : Bool}

theorem finishStoreFlag_present_old (ho : X.tensorStores i=some o) {e : Ref}
    (he : e≠.async i (storeDonePart stage)) :
    (X.finishStoreFlag i o stage).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j=i
    · subst j
      by_cases hp : p=.readsDone
      · subst p
        cases stage with
        | false => exact (he rfl).elim
        | true => simp [Execution.RefPresent,Execution.AsyncPresent,Execution.finishStoreFlag,
            Execution.storeDoneFlags,ho,TensorStore.Observation.doneFlags]
      · by_cases hp' : p=.fullDone
        · subst p
          cases stage with
          | true => exact (he rfl).elim
          | false => simp [Execution.RefPresent,Execution.AsyncPresent,Execution.finishStoreFlag,
              Execution.storeDoneFlags,ho,TensorStore.Observation.doneFlags]
        · exact storeDoneFlags_present_memory ho hp hp'
    · cases p <;> simp only [Execution.RefPresent,Execution.AsyncPresent,
        Execution.finishStoreFlag,Execution.storeDoneFlags,ite_eq_right hj]
      all_goals rfl

theorem no_store_done_object_before (ho : ObjectsOk X) {m : Loc} {f : Ref} :
    ¬Before (X.objects m) (.async i (storeDonePart stage)) f := by
  rintro ⟨j,k,n,w,hj,hid,_⟩
  have hs := ((ho m).2.1 n (List.mem_of_getElem? hj)).1
  cases stage <;> simp [storeDonePart,objectAction,hid] at hs

theorem finishStoreFlag_absent (ho : X.tensorStores i=some o)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false) :
    ¬ X.RefPresent (.async i (storeDonePart stage)) := by
  cases stage <;> simp only [Execution.RefPresent,storeDonePart,Bool.false_eq_true,ite_false,
    ite_true] at hn ⊢ <;> rintro ⟨o',ho',hflag⟩ <;> rw [ho] at ho' <;> cases ho' <;>
    rw [hn] at hflag <;> cases hflag

/-- The new completion flag leads only to its own completion point and to the returns of the
waits it witnesses. -/
theorem finishStoreFlag_waits_from
    (hok : TensorStore.CopyOk o.spec o.effects) (hobj : ObjectsOk X)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false)
    {b : Bool} {v : Ref × Bool}
    (h : Waits L (X.finishStoreFlag i o stage) (.async i (storeDonePart stage),b) v) :
    (v.1=.async i (storeDonePart stage) ∧ b=false ∧ v.2=true) ∨
      (b=false ∧ v.2=true ∧ ∃ w, v.1=.thread w ∧
        Witness L (X.finishStoreFlag i o stage) (.async i (storeDonePart stage)) w) := by
  rcases h with ⟨he,hb,hb',_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨hb,hb',ha⟩ | ⟨_,_,m,hm⟩ | ⟨j,k,he,_⟩ | ⟨hb,hb',w,hw,hwit⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ | ⟨j,k,he,_⟩ | ⟨_,_,j,k,he,_⟩ |
    ⟨_,_,j,k,he,_⟩ | ⟨_,_,hi⟩
  · exact .inl ⟨he.symm,hb,hb'⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · exfalso
    rcases ha with ⟨-,h0,-⟩ | ⟨-,-,ha⟩
    · rw [hb] at h0
      cases h0
    cases stage with
    | true => cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p => rw [hv] at ha; cases p <;> exact ha
    | false =>
      cases hv : v.1 with
      | thread j => rw [hv] at ha; exact ha
      | async j p =>
        rw [hv] at ha
        cases p <;> try exact ha
        case fullDone =>
          obtain ⟨hij,_,hfull⟩ := ha
          subst j
          have hd : o.effects.fullDone=true := by
            simpa [Execution.AsyncPresent,Execution.finishStoreFlag,Execution.storeDoneFlags,
              TensorStore.Observation.doneFlags] using hfull
          have hr := (hok.complete hd).1
          simp only [Bool.false_eq_true,ite_false] at hn
          rw [hn] at hr
          cases hr
  · exact (no_store_done_object_before hobj hm).elim
  · cases he
  · exact .inr ⟨hb,hb',w,hw,hwit⟩
  · cases he
  · cases he
  · cases he
  · cases he
  · cases he
  · obtain ⟨_,_,k,q,he,_⟩ := hi
    cases he

/-- The new completion flag and the returns of the group waits it witnesses form a sink of the
extension; outside them every order relation is old. -/
theorem finishStoreFlag_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o)
    (hok : TensorStore.CopyOk o.spec o.effects)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false) :
    SinkFrame L K A X (X.finishStoreFlag i o stage)
      (CompletionNodes L (X.finishStoreFlag i o stage) (· = .async i (storeDonePart stage))) := by
  have hobj : ObjectsOk X := hX.tma.2.2.1
  have hneeds : ∀ e, Needs L (X.finishStoreFlag i o stage) e = Needs L X e :=
    storeDoneFlags_needs hobj ho
  have hpres : ∀ {e : Ref}, e ≠ .async i (storeDonePart stage) →
      (X.finishStoreFlag i o stage).RefPresent e → X.RefPresent e :=
    fun he h => (finishStoreFlag_present_old ho he).mp h
  have hold : ∀ {u : Ref × Bool},
      ¬ CompletionNodes L (X.finishStoreFlag i o stage) (· = .async i (storeDonePart stage)) u →
      u.1 ≠ .async i (storeDonePart stage) := fun hu he => hu (.inl he)
  refine sinkFrame_completion (· = .async i (storeDonePart stage)) (fun _ h => by cases h)
    (fun u v hu h => ?_) (fun w x hx hw v => ?_) (fun u v hu hv hc => ?_)
    (fun x w hx hw h => ?_) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun u v hu hv hc => ?_) (fun m j p y hb => (hX.asyncObject m j p y hb).1)
    (fun _ _ _ _ _ _ h => h) hX.initFence (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    simp only at hu
    subst hu
    exact finishStoreFlag_waits_from hok hobj hn h
  · subst hx
    obtain ⟨hgw, hr⟩ := witness_absent_pending hX.dependency.ready (hneeds w)
      (finishStoreFlag_absent ho hn) hw
    exact groupWait_return_not_waits (X := X.finishStoreFlag i o stage) hgw (hgw.last hr)
      (fun m r hr' => hgw.not_record hobj hr') (fun c r hr' => hgw.not_cluster hX.cluster hr')
      (fun cta x hx' => hgw.not_participates hX.tmemPair hx') v
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | hc
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.finishStoreFlag i o stage)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl hc))
    · exact .single (.inr (.inr hc))
  · rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · exact .inl ⟨⟨hpres (hold hx) hm.1, hm.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres (hold hx) h3, h4, h5⟩
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | ⟨h1, h2, j, hj, fills, hn', hx, hf⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X) (Y := X.finishStoreFlag i o stage)
        (fun _ _ h => h) (fun _ _ h => h) (hpres (hold hu)) (hpres (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X) (Y := X.finishStoreFlag i o stage)
        (fun _ => rfl) (hpres (hold hv)) hc)))
    · rw [hneeds] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))

end
end PTX
end

section
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation} {stage : Bool}

def StoreFlagReady (o : TensorStore.Observation) (stage : Bool) : Prop :=
  if stage then o.effects.readsDone=true ∧
    ∀slot loc,TensorStore.destination o.spec slot=some loc → ∃b,o.effects.write slot=some b
  else ∀slot loc,TensorStore.destination o.spec slot=some loc → ∃b,o.effects.read slot=some b

 theorem finishStoreFlag_copyOk (hok : TensorStore.CopyOk o.spec o.effects)
    (hready : StoreFlagReady o stage) :
    TensorStore.CopyOk o.spec (o.doneFlags
      (if stage then o.effects.readsDone else true)
      (if stage then true else o.effects.fullDone)).effects := by
  cases stage with
  | false =>
    refine ⟨hok.writes,fun _ => hready,?_,hok.element,hok.old⟩
    intro hfull
    exact ⟨rfl,(hok.complete hfull).2⟩
  | true => exact ⟨hok.writes,hok.readsComplete,fun _ => hready,hok.element,hok.old⟩

 theorem consistent_finishStoreFlag {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false)
    (hready : StoreFlagReady o stage)
    (hasm : ∀a∈A,a.wf L mem0 (X.finishStoreFlag i o stage)) :
    Consistent L K A mem0 (X.finishStoreFlag i o stage) := by
  obtain ⟨hi,hvalid,hcopy⟩ := hX.store i o ho
  have hr : o.effects.readsDone=true → (if stage then o.effects.readsDone else true)=true := by
    cases stage <;> simp
  have hf : o.effects.fullDone=true → (if stage then true else o.effects.fullDone)=true := by
    cases stage <;> simp
  apply consistent_recordStoreEffects
    (o := o.doneFlags (if stage then o.effects.readsDone else true)
      (if stage then true else o.effects.fullDone)) (rf := X.rf)
    hX hi hvalid (finishStoreFlag_copyOk hcopy hready)
  · intro old hold
    have heq : old=o := Option.some.inj (hold.symm.trans ho)
    subst old
    exact storeDoneFlags_extends o _ _ hr hf
  · exact storeDoneFlags_rf hX.rf ho
  · exact (finishStoreFlag_sinkFrame hX ho hcopy hn).orderOk hX.orderOk
  · exact storeDoneFlags_noFuture hX.noFuture hX.dependency.ready hX.tma.2.2.1 ho
  · exact storeDoneFlags_hidden hX.hidden hX.dependency.ready hX.tma.2.2.1 ho
  · intros; rfl
  · exact recordStoreEffects_reduce hX.reduce
      (fun _ _ _ _ => ⟨o, ho, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩) (fun _ _ _ _ => rfl)
  · exact hasm
  · exact atomicOk_congr (X := X) (Y := X.finishStoreFlag i o stage)
      (fun p l n => by
        cases p with
        | tensor j x y =>
          by_cases hj : j = i
          · subst j
            simp [Execution.RmwAt, TensorStore.Reduced, Execution.finishStoreFlag,
              Execution.storeDoneFlags, ho, TensorStore.Observation.doneFlags,
              TensorStore.writeByte]
          · simp [Execution.RmwAt, TensorStore.Reduced, Execution.finishStoreFlag,
              Execution.storeDoneFlags, hj]
        | _ => exact Iff.rfl)
      (fun _ _ => rmwStrong_congr rfl rfl) (fun p k => by cases p <;> rfl) hX.atomic

 theorem finishStoreFlag_effect_size
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false) :
    (o.doneFlags (if stage then o.effects.readsDone else true)
      (if stage then true else o.effects.fullDone)).effects.size=o.effects.size+1 := by
  cases stage <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hn ⊢
  all_goals
    unfold TensorStore.Effects.size
    change o.effects.readSlots.card+o.effects.writeSlots.card+_+_=_
    simp only [TensorStore.Observation.doneFlags,hn,Bool.false_eq_true,↓reduceIte]
  omega

 theorem finishStoreFlag_asyncSize (ho : X.tensorStores i=some o)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false) {j : EvId} :
    (X.finishStoreFlag i o stage).asyncSize j=if j=i then X.asyncSize j+1 else X.asyncSize j := by
  unfold Execution.asyncSize
  rw [show (X.finishStoreFlag i o stage).async=X.async from rfl,
    show (X.finishStoreFlag i o stage).clc=X.clc from rfl,
    show (X.finishStoreFlag i o stage).tensor=X.tensor from rfl,
    show (X.finishStoreFlag i o stage).tcNotified=X.tcNotified from rfl,
    show (X.finishStoreFlag i o stage).elemSize=X.elemSize from rfl,
    show (X.finishStoreFlag i o stage).tensorStores j=if j=i then some (o.doneFlags
      (if stage then o.effects.readsDone else true) (if stage then true else o.effects.fullDone))
      else X.tensorStores j from rfl]
  by_cases hj : j=i
  · subst j
    simp only [↓reduceIte,ho,Option.map_some,Option.getD_some,finishStoreFlag_effect_size hn]
    omega
  · simp only [hj,↓reduceIte]

 theorem finishStoreFlag_size (ho : X.tensorStores i=some o)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false)
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) :
    (X.finishStoreFlag i o stage).size L=X.size L+1 := by
  have hs (j : EvId) := finishStoreFlag_asyncSize (j:=j) ho hn
  have heq (g k : Nat) : (g,k)=i ↔ g=i.1 ∧ k=i.2 := Prod.ext_iff
  have hthread (g : Nat) :
      ((List.range (X.tr g).length).map fun k => (X.finishStoreFlag i o stage).asyncSize (g,k)).sum=
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
          (if g=i.1 then 1 else 0) := by
    simp_rw [hs,heq]
    by_cases hg' : g=i.1
    · subst g
      simp only [true_and,↓reduceIte]
      exact sum_range_bump _ _ _ |>.trans (by rw [ite_eq_left hi])
    · simp only [hg',false_and,ite_false,Nat.add_zero]
  unfold Execution.size Execution.threadSize
  change ((List.range L.threads).map fun g =>
    (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k =>
        (X.finishStoreFlag i o stage).asyncSize (g,k)).sum).sum+
      X.pairSize L=_
  simp_rw [hthread]
  have hb := sum_range_bump
    (fun g => (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum) i.1 L.threads
  rw [ite_eq_left hg] at hb
  have hh : ∀g, (X.tr g).countP Event.counts+
      (((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+
        (if g=i.1 then 1 else 0))=
      if g=i.1 then (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum+1
      else (X.tr g).countP Event.counts+
        ((List.range (X.tr g).length).map fun k => X.asyncSize (g,k)).sum := by
    intro g
    split_ifs <;> omega
  simp_rw [hh]
  rw [hb]
  omega

end
end PTX
end
