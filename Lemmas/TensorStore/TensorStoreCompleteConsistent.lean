-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcReadSemanticFrame
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Tensor.TensorGrowth
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Execution.EffectFrame
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Execution.NeedFills

@[expose] public section

/-! Actual tensor-store effect updates. New byte RF/visibility and waiting
obligations remain explicit until the source protocol supplies their witnesses;
all unrelated execution constraints and old group waits are preserved here. -/
namespace PTX
open AsyncCopy
noncomputable section

def Execution.recordStoreEffects (X : Execution) (i : EvId)
    (o : TensorStore.Observation) (rf : Ref → Nat → Option Ref) : Execution :=
  {X with tensorStores:=fun j => if j=i then some o else X.tensorStores j,rf:=rf}

 theorem recordStoreEffects_snapshot {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hobs : ∀old,X.tensorStores i=some old → old.Extends o) :
    TensorStore.SnapshotExtends X.tensorStores (X.recordStoreEffects i o rf).tensorStores := by
  intro j old hold
  by_cases hj : j=i
  · subst j
    exact ⟨o,by simp [Execution.recordStoreEffects],hobs old hold⟩
  · exact ⟨old,by simpa only [Execution.recordStoreEffects,ite_eq_right hj] using hold,
      TensorStore.Observation.extends_refl _⟩

 theorem recordStoreEffects_store {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hX : TensorStoreOk L X) (hi : ∃address,X.TensorStoreIssue i address o.spec)
    (hv : TensorStore.Valid (i.1/L.block) o.spec) (hc : TensorStore.CopyOk o.spec o.effects) :
    TensorStoreOk L (X.recordStoreEffects i o rf) := by
  intro j old hold
  by_cases hj : j=i
  · subst j
    have hsame : o=old := by simpa [Execution.recordStoreEffects] using hold
    subst old
    exact ⟨hi,hv,hc⟩
  · exact hX j old (by simpa only [Execution.recordStoreEffects,ite_eq_right hj] using hold)

 theorem recordStoreEffects_present_record {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X)
    {m : Loc} {r : MBarrier.Record Ref} (hr : r ∈ X.objects m) :
    (X.recordStoreEffects i o rf).RefPresent r.id ↔ X.RefPresent r.id := by
  rcases record_id_cases ho hr with ⟨t, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, c, h⟩ | ⟨j, h⟩ | ⟨j, rk, h⟩ <;>
    rw [h] <;> exact Iff.rfl

/-- The needs of an event are unchanged by a tensor-store effect update. -/
theorem recordStoreEffects_needs {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X) (e : EvId) :
    Needs L (X.recordStoreEffects i o rf) e = Needs L X e := by
  refine needs_congr (L := L) (X := X) (Y := X.recordStoreEffects i o rf) (fun _ => rfl)
    (fun k e hk => ?_) (fun e m => ?_) e
  · cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl)
  · refine pollNeeds_congr (X := X) (Y := X.recordStoreEffects i o rf) (fun _ => rfl)
      (fun m r hr w => ?_) e m
    exact and_congr (recordStoreEffects_present_record ho hr) Iff.rfl

/-- Readiness survives a tensor-store effect update that extends the observation: the stages
that a group wait covers stay present. -/
theorem recordStoreEffects_ready {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X)
    (hobs : ∀old,X.tensorStores i=some old → old.Extends o)
    (hready : ∀ e, Returned X e → Ready L X e) :
    ∀ e, Returned (X.recordStoreEffects i o rf) e → Ready L (X.recordStoreEffects i o rf) e := by
  have hsnap := recordStoreEffects_snapshot (rf := rf) hobs
  refine ready_congr (X := X) (L := L) (recordStoreEffects_needs ho) (fun e h => h)
    (fun j fills x hn' hf hx => ?_) hready
  rcases needs_node_cases hn' hf with ⟨t, h⟩ | ⟨a, k, p, h, hp⟩ | ⟨m, r, hr, h⟩
  · subst h; exact hx
  · subst h
    rcases groupWaitStages_cases X a k hp with rfl | rfl | rfl | rfl
    · obtain ⟨old, hold, hdone⟩ := hx
      obtain ⟨newer, hnew, hs⟩ := hsnap a old hold
      rcases old with ⟨s, old⟩
      rcases newer with ⟨t, newer⟩
      obtain ⟨hsp, he⟩ := hs
      cases hsp
      exact ⟨⟨s, newer⟩, hnew, he.2.2.1 hdone⟩
    · obtain ⟨old, hold, hdone⟩ := hx
      obtain ⟨newer, hnew, hs⟩ := hsnap a old hold
      rcases old with ⟨s, old⟩
      rcases newer with ⟨t, newer⟩
      obtain ⟨hsp, he⟩ := hs
      cases hsp
      exact ⟨⟨s, newer⟩, hnew, he.2.2.2.1 hdone⟩
    · exact hx
    · exact hx
  · subst h; exact (recordStoreEffects_present_record ho hr).mpr hx

theorem recordStoreEffects_baseCausality_iff {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k) {e f : EvId} :
    baseCausality L (X.recordStoreEffects i o rf) e f ↔ baseCausality L X e f :=
  baseCausality_new_effect hrf

theorem recordStoreEffects_observesMma_iff {X : Execution} {i mma waiter : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.recordStoreEffects i o rf) mma .mmaDone waiter acq ws ↔
      AsyncObserved X mma .mmaDone waiter acq ws :=
  Iff.rfl

/-- TMA byte growth does not change any existing TMEM arithmetic source,
allocation history, stability order or completion observation. -/
theorem recordStoreEffects_semanticFrame {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k) :
    TcMma.SemanticFrame L X (X.recordStoreEffects i o rf) :=
  ⟨fun _ => rfl,fun _ => rfl,rfl,rfl,fun _ _ => recordStoreEffects_baseCausality_iff hrf,
    fun _ _ _ _ => recordStoreEffects_observesMma_iff,fun _ _ => Iff.rfl⟩


/-- The tensor-reduction rule survives an observation update that keeps every performed
reduction element and the sources of reduction reads. -/
theorem recordStoreEffects_reduce {A : List Assumption} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref} (hX : TensorStore.ReduceOk A X)
    (hi : o.spec.reduce.isSome → ∀ x y, (TensorStore.writeByte o x y 0).isSome →
      ∃ old, X.tensorStores i = some old ∧ old.spec = o.spec ∧ ∀ k,
        TensorStore.writeByte o x y k = TensorStore.writeByte old x y k ∧
        TensorStore.oldByte o x y k = TensorStore.oldByte old x y k ∧
        TensorStore.readByte o x y k = TensorStore.readByte old x y k)
    (_hrf : ∀ j x y k, rf (.async j (.old (.store x y k))) 0 =
      X.rf (.async j (.old (.store x y k))) 0) :
    TensorStore.ReduceOk A (X.recordStoreEffects i o rf) :=
  hX.frame (.update (fun _ => rfl) hi) fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩

/-- A performed reduction element of `X` stays performed, with the same footprint, after an
update that extends the observation. -/
theorem recordStoreEffects_reduced_mono {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {rf : Ref → Nat → Option Ref} (hobs : ∀old,X.tensorStores i=some old → old.Extends o)
    {j : EvId} {x y : Nat} {fp : Acc} (h : TensorStore.Reduced X j x y fp) :
    TensorStore.Reduced (X.recordStoreEffects i o rf) j x y fp := by
  obtain ⟨old, red, loc, ho, hr, hl, hfp, hw⟩ := h
  by_cases hj : j = i
  · subst hj
    obtain ⟨hsp, he⟩ := hobs old ho
    refine ⟨o, red, loc, by simp [Execution.recordStoreEffects], hsp ▸ hr, hsp ▸ hl, ?_, ?_⟩
    · rw [hfp]; congr 1; rw [← hsp]
    · rcases old with ⟨s, e⟩
      rcases o with ⟨t, e'⟩
      cases hsp
      unfold TensorStore.writeByte at hw ⊢
      cases hs : TensorTransfer.slotAt s.descriptor x y 0 with
      | none => simp [hs] at hw
      | some slot =>
        simp only [hs, Option.bind_some] at hw ⊢
        cases hv : e.write slot with
        | none => simp [hv] at hw
        | some b => rw [he.2.1 slot b hv]; rfl
  · exact ⟨old, red, loc, by simpa [Execution.recordStoreEffects, hj] using ho, hr, hl, hfp, hw⟩

/-- Atomicity transports across a tensor-store update that keeps every performed reduction
element (`ReduceFrame`) and the sources of every old-value read. -/
theorem recordStoreEffects_atomicOk {L : Launch} {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hX : AtomicOk L X) (hobs : ∀old,X.tensorStores i=some old → old.Extends o)
    (hfr : TensorStore.ReduceFrame X (X.recordStoreEffects i o rf))
    (hthreadRf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (hstoreRf : ∀j x y k,rf (.async j (.old (.store x y k))) 0=
      X.rf (.async j (.old (.store x y k))) 0)
    (hcopyRf : ∀j e k,rf (.async j (.old (.elem e))) k=X.rf (.async j (.old (.elem e))) k) :
    AtomicOk L (X.recordStoreEffects i o rf) :=
  atomicOk_congr (X := X) (Y := X.recordStoreEffects i o rf)
    (fun p l n => by
      cases p with
      | thread e => exact Iff.rfl
      | copy j e => exact Iff.rfl
      | tensor j x y =>
        exact ⟨fun ⟨fp, h, h1, h2⟩ => ⟨fp, hfr.reduced h, h1, h2⟩,
          fun ⟨fp, h, h1, h2⟩ => ⟨fp, recordStoreEffects_reduced_mono hobs h, h1, h2⟩⟩)
    (fun p q => by cases p <;> cases q <;> exact Iff.rfl)
    (fun p k => by
      cases p with
      | thread e => exact hthreadRf e k
      | tensor j x y => exact hstoreRf j x y k
      | copy j e => exact hcopyRf j e k) hX

theorem consistent_recordStoreEffects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {rf : Ref → Nat → Option Ref}
    (hX : Consistent L K A mem0 X) (hi : ∃address,X.TensorStoreIssue i address o.spec)
    (hv : TensorStore.Valid (i.1/L.block) o.spec) (hc : TensorStore.CopyOk o.spec o.effects)
    (hobs : ∀old,X.tensorStores i=some old → old.Extends o)
    (hr : RfWf mem0 (X.recordStoreEffects i o rf))
    (ha : OrderOk L K A (X.recordStoreEffects i o rf))
    (hf : NoFuture L (X.recordStoreEffects i o rf))
    (hh : Hidden L (X.recordStoreEffects i o rf))
    (hthreadRf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (hred : TensorStore.ReduceOk A (X.recordStoreEffects i o rf))
    (hasm : ∀a∈A,a.wf L mem0 (X.recordStoreEffects i o rf))
    (hatomic : AtomicOk L (X.recordStoreEffects i o rf)) :
    Consistent L K A mem0 (X.recordStoreEffects i o rf) := by
  exact { hX with
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
    rf := hr
    dependency := ⟨recordStoreEffects_ready hX.tma.2.2.1 hobs hX.dependency.ready, ha.depAcyclic⟩
    observation := ha.observation
    object := ha.object
    asyncObject := ha.asyncObject
    initFence := ha.initFence
    noFuture := hf
    hidden := hh
    store := recordStoreEffects_store hX.store hi hv hc
    atomic := hatomic
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
      hX.fenceSc.causal e f hs ((recordStoreEffects_baseCausality_iff hthreadRf).mp h)⟩
    tcRead := (recordStoreEffects_semanticFrame hthreadRf).readOk.mpr hX.tcRead
    reduce := hred
    asm := hasm }

 theorem Execution.le_recordStoreEffects {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hobs : ∀old,X.tensorStores i=some old → old.Extends o)
    (hrf : ∀e k,(∃a bs,X.MemReads e a bs) → rf e k=X.rf e k) :
    X.le (X.recordStoreEffects i o rf) := by
  obtain ⟨ht,_,ha,ho,hb,hc,hcl,hcs,hload,_,hp,hpb,hn⟩ := Execution.le_refl X
  exact ⟨ht,hrf,ha,ho,hb,hc,hcl,hcs,hload,recordStoreEffects_snapshot hobs,hp,hpb,hn⟩

 theorem recordStoreEffects_size_of_measure {X : Execution} {L : Launch} {i : EvId}
    {o : TensorStore.Observation} {rf : Ref → Nat → Option Ref}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length)
    (hs : ((X.tensorStores i).map (fun old => old.effects.size)).getD 0<o.effects.size) :
    X.size L<(X.recordStoreEffects i o rf).size L := by
  have hstrict : X.asyncSize i<(X.recordStoreEffects i o rf).asyncSize i := by
    simp only [Execution.asyncSize,Execution.recordStoreEffects,↓reduceIte,Option.map_some,
      Option.getD_some]
    exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_left hs _) _) _
  apply Execution.size_lt_of_asyncStages (X:=X) (Y:=X.recordStoreEffects i o rf)
    rfl (Nat.le_refl _) hg hi ?_ hstrict
  intro j
  by_cases hj : j=i
  · subst j
    exact hstrict.le
  · simp only [Execution.asyncSize,Execution.recordStoreEffects,hj,↓reduceIte]
    exact Nat.le_refl _

end
end PTX
