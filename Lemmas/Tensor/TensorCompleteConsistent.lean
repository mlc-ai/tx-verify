-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcReadSemanticFrame
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Tensor.TensorGrowth
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Async.AsyncExecution
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Execution.EffectFrame
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Execution.NeedFills

@[expose] public section

/-! Growing the read/write stages of one tensor load. Object notifications are
unchanged by this update; the exact memory and waiting obligations for newly
recorded bytes remain explicit. No successful operation is assumed implicitly. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- Record independent TMA byte effects and their chosen read sources. -/
def Execution.recordTensorEffects (X : Execution) (i : EvId)
    (o : TensorCopy.Observation) (rf : Ref → Nat → Option Ref) : Execution :=
  {X with tensor := fun j => if j=i then some o else X.tensor j, rf := rf}

theorem recordTensorEffects_objectAction {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified)) :
    ∀m id, objectAction (X.recordTensorEffects i o rf) X.async m id=
      objectAction X X.async m id := by
  intro m id
  have hget : (X.recordTensorEffects i o rf).get=X.get := rfl
  cases id with
  | thread j => rfl
  | async j part =>
    cases part <;> try rfl
    case notifyLoad =>
      by_cases hj : j=i
      · subst j
        have hti : (X.recordTensorEffects i o rf).tensor i=some o := by
          simp [Execution.recordTensorEffects]
        simp only [objectAction,hget,hti]
        cases hg : X.get i with
        | none => simp only
        | some ev =>
          rcases ev with ⟨pc,kind⟩
          cases kind <;> simp only [bind,Option.bind]
          rename_i address spec
          cases ho : X.tensor i with
          | none =>
            have hn' : o.effects.notified=false := by simpa only [ho,Option.any_none] using hn
            simp [hn']
          | some old =>
            have hn' : o.effects.notified=old.effects.notified := by
              simpa only [ho,Option.any_some] using hn
            simp [hn']
      · have htj : (X.recordTensorEffects i o rf).tensor j=X.tensor j := by
          simp [Execution.recordTensorEffects,hj]
        simp only [objectAction,hget,htj]

/-- Tensor byte effects do not release unrelated generic accesses. Keeping
thread read sources fixes every base happens-before edge. -/
theorem recordTensorEffects_baseCausality_iff {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k) {e f : EvId} :
    baseCausality L (X.recordTensorEffects i o rf) e f ↔ baseCausality L X e f :=
  baseCausality_new_effect hrf

/-- A notified observation of the update is a notified observation of `X` with its spec. -/
theorem recordTensorEffects_notified {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hn : o.effects.notified=true →
      ∃old,X.tensor i=some old ∧ old.spec=o.spec ∧ old.effects.notified=true) :
    ∀j obs,(X.recordTensorEffects i o rf).tensor j=some obs → obs.effects.notified=true →
      ∃old,X.tensor j=some old ∧ old.spec=obs.spec ∧ old.effects.notified=true := by
  intro j obs h hobs
  by_cases hj : j=i
  · subst j
    have he : o=obs := by simpa [Execution.recordTensorEffects] using h
    subst obs
    exact hn hobs
  · exact ⟨obs,by simpa [Execution.recordTensorEffects,hj] using h,rfl,hobs⟩

theorem recordTensorEffects_observesMma_iff {X : Execution} {i mma waiter : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.recordTensorEffects i o rf) mma .mmaDone waiter acq ws ↔
      AsyncObserved X mma .mmaDone waiter acq ws :=
  Iff.rfl

/-- TMA byte growth does not change any existing TMEM arithmetic source,
allocation history, stability order or completion observation. -/
theorem recordTensorEffects_semanticFrame {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k) :
    TcMma.SemanticFrame L X (X.recordTensorEffects i o rf) :=
  ⟨fun _ => rfl,fun _ => rfl,rfl,rfl,fun _ _ => recordTensorEffects_baseCausality_iff hrf,
    fun _ _ _ _ => recordTensorEffects_observesMma_iff,fun _ _ => Iff.rfl⟩

theorem recordTensorEffects_tma {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (h : TmaOk X)
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified)) :
    TmaOk (X.recordTensorEffects i o rf) := by
  refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
  intro m
  obtain ⟨hc,hm,hcover⟩ := h.2.2.1 m
  refine ⟨hc,?_,?_⟩
  · intro r hr
    have hh := hm r hr
    exact ⟨(recordTensorEffects_objectAction hn m r.id).trans hh.1,hh.2⟩
  · intro id action ha
    have ha' := (recordTensorEffects_objectAction hn m id).symm.trans ha
    exact hcover id action ha'

/-- The id of a recorded update is present after the update exactly when it was before. -/
theorem recordTensorEffects_present_record {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X)
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified))
    {m : Loc} {r : MBarrier.Record Ref} (hr : r ∈ X.objects m) :
    (X.recordTensorEffects i o rf).RefPresent r.id ↔ X.RefPresent r.id := by
  rcases record_id_cases ho hr with ⟨t, h⟩ | ⟨j, h⟩ | ⟨j, h⟩ | ⟨j, c, h⟩ | ⟨j, h⟩ | ⟨j, rk, h⟩ <;>
    rw [h]
  case inr.inr.inl =>
    simp only [Execution.RefPresent, Execution.AsyncPresent, Execution.recordTensorEffects]
    by_cases hj : j = i
    · subst hj
      cases hx : X.tensor j <;> simp [hx] at hn ⊢
      · simp [hn]
      · simp [hn]
    · simp [hj]
  all_goals exact Iff.rfl

/-- The needs of an event are unchanged by a tensor-effect update. -/
theorem recordTensorEffects_needs {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X)
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified)) (e : EvId) :
    Needs L (X.recordTensorEffects i o rf) e = Needs L X e := by
  refine needs_congr (L := L) (X := X) (Y := X.recordTensorEffects i o rf) (fun _ => rfl)
    (fun k e hk => ?_) (fun e m => ?_) e
  · cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl)
  · refine pollNeeds_congr (X := X) (Y := X.recordTensorEffects i o rf) (fun _ => rfl)
      (fun m r hr w => ?_) e m
    exact and_congr (recordTensorEffects_present_record ho hn hr) Iff.rfl

/-- Readiness survives a tensor-effect update. -/
theorem recordTensorEffects_ready {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref} (ho : ObjectsOk X)
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified))
    (hready : ∀ e, Returned X e → Ready L X e) :
    ∀ e, Returned (X.recordTensorEffects i o rf) e → Ready L (X.recordTensorEffects i o rf) e := by
  refine ready_congr (X := X) (L := L) (recordTensorEffects_needs ho hn) (fun e h => h)
    (fun j fills x hn' hf hx => ?_) hready
  rcases needs_node_cases hn' hf with ⟨t, h⟩ | ⟨a, k, p, h, hp⟩ | ⟨m, r, hr, h⟩
  · subst h; exact hx
  · subst h
    rcases groupWaitStages_cases X a k hp with rfl | rfl | rfl | rfl <;> exact hx
  · subst h; exact (recordTensorEffects_present_record ho hn hr).mpr hx

theorem recordTensorEffects_tensor {L : Launch} {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (h : TensorOk L X) (hi : ∃address,X.TensorIssue i address o.spec)
    (hc : TensorCopy.CopyOk o.spec o.effects)
    (hr : TensorCopy.RoutingOk L (i.1/L.block) o.spec)
    (hv : TensorDescriptor.Valid o.spec.descriptor) :
    TensorOk L (X.recordTensorEffects i o rf) := by
  intro j old ho
  by_cases hj : j=i
  · subst j
    have he : o=old := by simpa [Execution.recordTensorEffects] using ho
    subst old
    exact ⟨hi,hc,hr,hv⟩
  · have ho' : X.tensor j=some old := by
      simpa only [Execution.recordTensorEffects,ite_eq_right hj] using ho
    exact h j old ho'

/-- Actual Consistent effect growth. Newly recorded byte RF, visibility and
waiting constraints are exposed; all unrelated collective/resource constraints
are transported from the same execution instead of re-assumed. -/
theorem consistent_recordTensorEffects {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {rf : Ref → Nat → Option Ref}
    (hX : Consistent L K A mem0 X)
    (hi : ∃address,X.TensorIssue i address o.spec)
    (hc : TensorCopy.CopyOk o.spec o.effects)
    (hrouting : TensorCopy.RoutingOk L (i.1/L.block) o.spec)
    (hv : TensorDescriptor.Valid o.spec.descriptor)
    (hn : o.effects.notified=(X.tensor i).any (fun old => old.effects.notified))
    (hr : RfWf mem0 (X.recordTensorEffects i o rf))
    (ha : OrderOk L K A (X.recordTensorEffects i o rf))
    (hf : NoFuture L (X.recordTensorEffects i o rf))
    (hh : Hidden L (X.recordTensorEffects i o rf))
    (hthreadRf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (hstoreRf : ∀j x y k,rf (.async j (.old (.store x y k))) 0=
      X.rf (.async j (.old (.store x y k))) 0)
    (hasm : ∀a∈A,a.wf L mem0 (X.recordTensorEffects i o rf))
    (hcopyRf : ∀j e k,rf (.async j (.old (.elem e))) k=X.rf (.async j (.old (.elem e))) k) :
    Consistent L K A mem0 (X.recordTensorEffects i o rf) where
  thr := hX.thr
  outside := hX.outside
  rf := hr
  ctaBar := hX.ctaBar
  cluster := hX.cluster
  dependency := ⟨recordTensorEffects_ready hX.tma.2.2.1 hn hX.dependency.ready, ha.depAcyclic⟩
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
  tma := recordTensorEffects_tma hX.tma hn
  clc := hX.clc
  tensor := recordTensorEffects_tensor hX.tensor hi hc hrouting hv
  store := hX.store
  reduce := hX.reduce.of_tensorStores rfl fun _ _ _ _ hc _ _ => ⟨hc, rfl⟩
  atomic := atomicOk_congr (X := X) (Y := X.recordTensorEffects i o rf)
    (fun p l n => by cases p <;> exact Iff.rfl) (fun _ _ => Iff.rfl)
    (fun p k => by
      cases p with
      | thread e => exact hthreadRf e k
      | tensor j x y => exact hstoreRf j x y k
      | copy j e => exact hcopyRf j e k) hX.atomic
  fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs h =>
    hX.fenceSc.causal e f hs ((recordTensorEffects_baseCausality_iff hthreadRf).mp h)⟩
  tmemPair := hX.tmemPair
  tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
  tmemPairResult := hX.tmemPairResult
  tcCommit := hX.tcCommit
  mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
  tcRead := (recordTensorEffects_semanticFrame hthreadRf).readOk.mpr hX.tcRead
  asm := hasm

/-- The exact extension relation retains prior byte effects and every old read
source. Missing observations need no artificial prior snapshot. -/
theorem Execution.le_recordTensorEffects {X : Execution} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hobs : ∀old,X.tensor i=some old → old.Extends o)
    (hrf : ∀e k,(∃a bs,X.MemReads e a bs) → rf e k=X.rf e k) :
    X.le (X.recordTensorEffects i o rf) := by
  obtain ⟨ht,_,ha,ho,hb,hc,hcl,hcs,_,hs,hp,hpb,hn⟩ := Execution.le_refl X
  refine ⟨ht,hrf,ha,ho,hb,hc,hcl,hcs,?_,hs,hp,hpb,hn⟩
  intro j old hold
  by_cases hj : j=i
  · subst j
    refine ⟨o,?_,hobs old hold⟩
    simp [recordTensorEffects]
  · refine ⟨old,?_,TensorCopy.Observation.extends_refl old⟩
    simpa only [recordTensorEffects,ite_eq_right hj] using hold

/-- Size growth also applies to an issue with no observation yet. -/
theorem recordTensorEffects_size_of_measure {X : Execution} {L : Launch} {i : EvId}
    {o : TensorCopy.Observation} {rf : Ref → Nat → Option Ref}
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length)
    (hs : ((X.tensor i).map (fun old => old.effects.size)).getD 0<o.effects.size) :
    X.size L<(X.recordTensorEffects i o rf).size L := by
  have hstrict : X.asyncSize i<(X.recordTensorEffects i o rf).asyncSize i := by
    simp only [Execution.asyncSize,Execution.recordTensorEffects,↓reduceIte,Option.map_some,
      Option.getD_some]
    exact Nat.add_lt_add_right (Nat.add_lt_add_right (Nat.add_lt_add_right
      (Nat.add_lt_add_left hs _) _) _) _
  apply Execution.size_lt_of_asyncStages (X := X) (Y := X.recordTensorEffects i o rf) rfl
    (Nat.le_refl _) hg hi ?_ hstrict
  intro j
  by_cases hj : j=i
  · subst j
    exact hstrict.le
  · simp only [Execution.asyncSize,Execution.recordTensorEffects,hj,↓reduceIte]
    exact Nat.le_refl _

end
end PTX
