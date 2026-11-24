-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.StoreDone
public import Lemmas.Step.WfInOrder
public import Lemmas.Step.DrainInOrder

@[expose] public section

/-! # An issued tensor store completes, under in-order assumptions

The in-order variant of `Lemmas/Step/StoreDone.lean`, for kernels whose assumptions constrain
executions (`Assumption.WfStep sel`). Each extension that records a store's step performs no
commit arrive-on and adds no read, so it keeps the constraints (`Assumption.WfStep.quiet`); the
chain repeats the proofs of `StoreDone.lean` with that argument in place of the all-extensions
premise. The read-source condition `VisibleReadSources` is shared. -/

namespace PTX.Step.StoreDone
open PTX AsyncCopy TensorStore
noncomputable section

variable {L : Launch} {mem0 : Mem0} {K : Kernel} {A : List Assumption} {X : Execution}
  {sel : Nat → Bool}

theorem flag_counted_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {stage : Bool}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hn : (if stage then o.effects.fullDone else o.effects.readsDone)=false)
    (hready : StoreFlagReady o stage) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ Y.size L=X.size L+1 := by
  have hle : X.le (X.finishStoreFlag i o stage) := by
    apply storeDoneFlags_le ho
    · cases stage <;> simp
    · cases stage <;> simp
  have hY := consistent_finishStoreFlag hX ho hn hready (hA.quiet hX hle rfl
      (Execution.noNewRead_of_tr rfl))
  refine ⟨X.finishStoreFlag i o stage,hY,hle,?_⟩
  · obtain ⟨address,pc,he⟩ := (hX.store i o ho).1
    have hg : i.1<L.threads := by
      by_contra hno
      have ht := hX.outside i.1 (by omega)
      have hi := len_of_get he
      rw [ht] at hi
      simp at hi
    exact finishStoreFlag_size ho hn hg (len_of_get he)

theorem reads_done_counted_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hn : o.effects.readsDone=false)
    (hreads : ∀slot loc,TensorStore.destination o.spec slot=some loc →
      ∃b,o.effects.read slot=some b) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ Y.size L=X.size L+1 :=
  flag_counted_inOrder (stage:=false) hA hX ho hn hreads

theorem full_done_counted_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false) (hreads : o.effects.readsDone=true)
    (hwrites : ∀slot loc,TensorStore.destination o.spec slot=some loc →
      ∃b,o.effects.write slot=some b) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ Y.size L=X.size L+1 :=
  flag_counted_inOrder (stage:=true) hA hX ho hn ⟨hreads,hwrites⟩


theorem read_of_latest_writer_counted_inOrder {X : Execution}
    {i : EvId} {o : TensorStore.Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {loc : Loc} {value : Byte} {w : Ref} {dst : Acc} {written : List Byte}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hloc : destination o.spec slot=some loc) (hmissing : o.effects.read slot=none)
    (hw : X.MemWrites w dst written) (hcover : dst.Covers (o.spec.sharedLoc slot))
    (hvalue : wbyte dst written (o.spec.sharedLoc slot)=some value)
    (hlatest : ∀other footprint bytes,X.MemWrites other footprint bytes →
      footprint.Covers (o.spec.sharedLoc slot) →
      ByteCausality L X (o.spec.sharedLoc slot) other (storeSlotReadRef i slot) →
      ¬ByteCausality L X (o.spec.sharedLoc slot) w other) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L := by
  obtain ⟨hi,hvalid,hcopy⟩ := hX.store i o ho
  have hn := missing_required_before_readDone hcopy hloc hmissing
  let rf : Ref → Nat → Option Ref := fun e k =>
    if e=storeSlotReadRef i slot then some w else X.rf e k
  have hobs : ∀old,X.tensorStores i=some old → old.Extends (o.readSlot slot value) := by
    intro old hold
    have heq := Option.some.inj (ho.symm.trans hold)
    subst old
    exact readSlot_extends hn hmissing
  have hz : Consistent L K A mem0 (X.recordStoreRead i o slot value (some w)) := by
    apply consistent_recordStoreEffects (o:=o.readSlot slot value) (rf:=rf) hX hi hvalid
      (readSlot_copyOk hcopy hn hmissing) hobs
    · exact storeReadFrame_rf_of_write hX ho hmissing hw hcover hvalue
    · exact storeReadWaiting_order hX ho hmissing hn
    · exact storeReadFrame_noFuture hX ho hn hmissing
    · exact storeReadFrame_hidden_of_latest hX ho hn hmissing hlatest
    · exact storeReadFrame_thread_rf (X:=X) (i:=i) (o:=o) (slot:=slot)
        (value:=value) (source:=some w)
    · exact recordStoreEffects_reduce hX.reduce
        (fun hr x y hw => ⟨o,ho,rfl,readSlot_reduced hcopy hmissing hr hw⟩)
        (fun _ _ _ _ => ite_eq_right (by simp [storeSlotReadRef]))
    · exact hA.quiet hX (storeReadFrame_le ho hn hmissing) rfl (Execution.noNewRead_of_tr rfl)
    · exact recordStoreEffects_atomicOk hX.atomic hobs
        (.update (fun _ => rfl) (fun hr x y hw => ⟨o,ho,rfl,readSlot_reduced hcopy hmissing hr hw⟩))
        (storeReadFrame_thread_rf (X:=X) (i:=i) (o:=o) (slot:=slot) (value:=value)
          (source:=some w))
        (fun _ _ _ _ => ite_eq_right (by simp [storeSlotReadRef]))
        (fun _ _ _ => ite_eq_right (by simp [storeSlotReadRef]))
  refine ⟨X.recordStoreRead i o slot value (some w),hz,storeReadFrame_le ho hn hmissing,?_⟩
  obtain ⟨address,pc,hissue⟩ := hi
  have hg : i.1<L.threads := by
    by_contra hno
    have htrace := hX.outside i.1 (Nat.le_of_not_gt hno)
    have hindex := len_of_get hissue
    rw [htrace] at hindex
    simp at hindex
  exact storeReadFrame_size ho hmissing hg (len_of_get hissue)


theorem byte_counted_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} {loc : Loc}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hred : o.spec.reduce=none) (hd : TensorStore.destination o.spec slot=some loc)
    (hr : o.effects.read slot=some value) (hn : o.effects.write slot=none) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L := by
  have hY := consistent_storeWrite hX ho hred hd hr hn (hA.quiet hX (storeWriteFrame_le ho hn) rfl
      (Execution.noNewRead_of_tr rfl))
  refine ⟨X.recordStoreWrite i o slot value,hY,storeWriteFrame_le ho hn,?_⟩
  obtain ⟨address,pc,he⟩ := (hX.store i o ho).1
  have hg : i.1<L.threads := by
    by_contra hno
    have ht := hX.outside i.1 (by omega)
    have hi := len_of_get he
    rw [ht] at hi
    simp at hi
  apply recordStoreEffects_size_of_measure hg (len_of_get he)
  simpa only [ho,Option.map_some,Option.getD_some] using
    Nat.lt_of_lt_of_eq (Nat.lt_succ_self o.effects.size) (TensorStore.writeSlot_size hn).symm


theorem pending_observation_of_read_progress_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false)
    (hread : ∀slot loc,TensorStore.destination o.spec slot=some loc → o.effects.read slot=none →
      ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L)
    (hreduce : ∀red,o.spec.reduce=some red → o.effects.readsDone=true →
      ∀slot loc,TensorStore.destination o.spec slot=some loc → o.effects.write slot=none →
      ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L := by
  classical
  by_cases hm : ∃slot loc,TensorStore.destination o.spec slot=some loc ∧ o.effects.read slot=none
  · obtain ⟨slot,loc,hd,hr⟩ := hm
    exact hread slot loc hd hr
  have hreads : ∀slot loc,TensorStore.destination o.spec slot=some loc →
      ∃b,o.effects.read slot=some b := by
    intro slot loc hd
    cases hr : o.effects.read slot with
    | none => exact False.elim (hm ⟨slot,loc,hd,hr⟩)
    | some b => exact ⟨b,rfl⟩
  cases hrDone : o.effects.readsDone with
  | false =>
    obtain ⟨Y,hY,hle,hs⟩ := reads_done_counted_inOrder hA hX ho hrDone hreads
    exact ⟨Y,hY,hle,by omega⟩
  | true =>
    by_cases hw : ∃slot loc,TensorStore.destination o.spec slot=some loc ∧ o.effects.write slot=none
    · obtain ⟨slot,loc,hd,hnw⟩ := hw
      obtain ⟨value,hr⟩ := hreads slot loc hd
      cases hred : o.spec.reduce with
      | none => exact byte_counted_inOrder hA hX ho hred hd hr hnw
      | some red => exact hreduce red hred hrDone slot loc hd hnw
    have hwrites : ∀slot loc,TensorStore.destination o.spec slot=some loc →
        ∃b,o.effects.write slot=some b := by
      intro slot loc hd
      cases hwr : o.effects.write slot with
      | none => exact False.elim (hw ⟨slot,loc,hd,hwr⟩)
      | some b => exact ⟨b,rfl⟩
    obtain ⟨Y,hY,hle,hs⟩ := full_done_counted_inOrder hA hX ho hn hrDone hwrites
    exact ⟨Y,hY,hle,by omega⟩


theorem pending_observation_visible_inOrder {X : Execution} {i : EvId}
    {o : TensorStore.Observation}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false) (hsource : VisibleReadSources L X i o.spec)
    (hsg : SyncGuarded L K X) (hstore : o.spec.reduce=none) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L := by
  refine pending_observation_of_read_progress_inOrder hA hX ho hn ?_
    (fun red hred => by rw [hstore] at hred; cases hred)
  intro slot loc hd hr
  obtain ⟨hex,hbytes⟩ := hsource slot loc hd
  obtain ⟨w,a,bs,value,hw,hcover,hvalue,_,hlatest⟩ :=
    exists_storeProgress_latest_visible hX hsg hex hbytes
  exact read_of_latest_writer_counted_inOrder hA hX ho hd hr hw hcover hvalue hlatest

/-- A store issue not yet fully done makes counted progress, for any read-source
condition `S` that survives zero-size initialization and supports progress of
an existing pending observation. -/
theorem pending_issue_of_inOrder {i : EvId} {spec : TensorStore.Spec}
    (S : Execution → TensorStore.Spec → Prop)
    (hinit : ∀{X : Execution},X.tensorStores i=none → S X spec →
      S (X.initStoreObservation i spec) spec)
    (hprogress : ∀{X : Execution} {o : TensorStore.Observation},
      Consistent L K A mem0 X → X.tensorStores i=some o → o.effects.fullDone=false →
      S X o.spec → ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L)
    {X : Execution}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (hi : ∃address,X.TensorStoreIssue i address spec)
    (hvalid : TensorStore.Valid (i.1/L.block) spec)
    (hn : ¬∃o,X.tensorStores i=some o ∧ o.effects.fullDone=true) (hsource : S X spec) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L := by
  cases ho : X.tensorStores i with
  | none =>
    have hz : Consistent L K A mem0 (X.initStoreObservation i spec) :=
      storeInit_consistent hX hi hvalid ho (hA.quiet hX (storeInit_le ho) rfl
          (Execution.noNewRead_of_tr rfl))
    obtain ⟨Y,hY,hle,hsize⟩ := hprogress hz
      (storeInit_observation (X:=X) (i:=i) (spec:=spec)) rfl (hinit ho hsource)
    exact ⟨Y,hY,Execution.le_trans (storeInit_le ho) hle,by rwa [storeInit_size ho] at hsize⟩
  | some o =>
    obtain ⟨address,pc,he⟩ := hi
    obtain ⟨⟨address',pc',he'⟩,_,_⟩ := hX.store i o ho
    have hs : o.spec=spec := by
      rw [he] at he'
      cases he'
      rfl
    have hnot : o.effects.fullDone=false := by
      cases hb : o.effects.fullDone with
      | false => rfl
      | true => exact False.elim (hn ⟨o,ho,hb⟩)
    exact hprogress hX ho hnot (by simpa only [hs] using hsource)


/-- **An issued store makes counted progress** once every byte it reads has a visible source. -/
theorem pending_issue_visible_inOrder {i : EvId} {spec : TensorStore.Spec}
    (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    (hi : ∃address,X.TensorStoreIssue i address spec)
    (hvalid : TensorStore.Valid (i.1/L.block) spec)
    (hn : ¬∃o,X.tensorStores i=some o ∧ o.effects.fullDone=true)
    (hsource : VisibleReadSources L X i spec) (hsg : SyncGuarded L K X)
    (hstore : spec.reduce=none) :
    ∃Y,Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L<Y.size L :=
  pending_issue_of_inOrder
    (fun X spec => VisibleReadSources L X i spec ∧ SyncGuarded L K X ∧ spec.reduce=none)
    (fun hn' hs => ⟨visibleReadSources_init hn' hs.1,
      ⟨hs.2.1.spin, hs.2.1.noMemSync, hs.2.1.noFault⟩,
      hs.2.2⟩)
    (fun hX' ho hn' hs' =>
      pending_observation_visible_inOrder hA hX' ho hn' hs'.1 hs'.2.1 hs'.2.2) hA hX hi
    hvalid hn ⟨hsource, hsg, hstore⟩


end
end PTX.Step.StoreDone
