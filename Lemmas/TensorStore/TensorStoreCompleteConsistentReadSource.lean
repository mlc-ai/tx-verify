-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistentRead
public import Lemmas.TensorStore.TensorStoreCompleteConsistentByteVisibility
public import Lemmas.Execution.EffectFrame
public import Lemmas.Async.AsyncOrder

@[expose] public section

section
namespace PTX
open AsyncCopy TensorStore
noncomputable section

def storeSlotReadRef (i : EvId) {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) : Ref :=
  .async i (.read (.store slot.1.val slot.2.1.val slot.2.2.val))

def Execution.recordStoreRead (X : Execution) (i : EvId) (o : TensorStore.Observation)
    (slot : TensorTransfer.Slot o.spec.descriptor) (value : Byte)
    (source : Option Ref) : Execution :=
  X.recordStoreEffects i (o.readSlot slot value)
    (fun e k => if e=storeSlotReadRef i slot then source else X.rf e k)

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {source : Option Ref}
local notation "Y" => X.recordStoreRead i o slot value source

theorem storeReadFrame_no_old_read (ho : X.tensorStores i=some o)
    (hmissing : o.effects.read slot=none) (a : Acc) (bs : List (Option Byte)) :
    ¬X.MemReads (storeSlotReadRef i slot) a bs := by
  rintro ⟨old,address,b,hobs,hissue,hloc,hread,_,_⟩
  have heq : o=old := Option.some.inj (ho.symm.trans hobs)
  subst old
  rw [readByte_slot,hmissing] at hread
  cases hread

theorem storeReadFrame_reads_other (ho : X.tensorStores i=some o) {e : Ref}
    (hne : e≠storeSlotReadRef i slot) (a : Acc) (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readStore x y k =>
      by_cases hj : j=i
      · subst j
        have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
          rintro ⟨rfl,rfl,rfl⟩
          exact hne rfl
        simp only [Execution.MemReads,Execution.recordStoreRead,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rw [readSlot_readByte_other hcoords]
        rfl
      · simp only [Execution.MemReads,Execution.recordStoreRead,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl
    case oldStore x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemReads,Execution.recordStoreRead,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemReads,Execution.recordStoreRead,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem storeReadFrame_writes (ho : X.tensorStores i=some o) (e : Ref) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeStore x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemWrites,Execution.recordStoreRead,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemWrites,Execution.recordStoreRead,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl


theorem storeReadFrame_reads_self {a : Acc} {bs : List (Option Byte)}
    (he : (Y).MemReads (storeSlotReadRef i slot) a bs) :
    a.loc=o.spec.sharedLoc slot ∧ a.size=1 ∧ bs=[some value] := by
  obtain ⟨old,mapAddress,b,hobs,hissue,hloc,hread,hsize,hbs⟩ := he
  have ht : (Y).tensorStores i=some (o.readSlot slot value) := by
    simp [Execution.recordStoreRead,Execution.recordStoreEffects]
  have heq := Option.some.inj (ht.symm.trans hobs)
  subst old
  have hbyte : TensorStore.readByte (o.readSlot slot value)
      slot.1.val slot.2.1.val slot.2.2.val=some value := by
    simp [TensorStore.readByte,TensorStore.Observation.readSlot,TensorCopy.slotAt_self]
  have hb : b=value := Option.some.inj (hread.symm.trans hbyte)
  have hlocation : TensorStore.readLoc (o.readSlot slot value).spec
      slot.1.val slot.2.1.val slot.2.2.val=some (o.spec.sharedLoc slot) := by
    simp [TensorStore.Observation.readSlot,TensorStore.readLoc,TensorCopy.slotAt_self]
  exact ⟨Option.some.inj (hloc.symm.trans hlocation),hsize,by simpa only [hb] using hbs⟩

theorem storeReadFrame_thread_rf (e : EvId) (k : Nat) :
    (Y).rf (.thread e) k=X.rf (.thread e) k := by
  simp [Execution.recordStoreRead,Execution.recordStoreEffects,storeSlotReadRef]

theorem storeReadFrame_le (ho : X.tensorStores i=some o)
    (hn : o.effects.readsDone=false) (hmissing : o.effects.read slot=none) : X.le Y := by
  apply Execution.le_recordStoreEffects
  · intro old hold
    have heq := Option.some.inj (ho.symm.trans hold)
    subst old
    exact readSlot_extends hn hmissing
  · intro e k hread
    by_cases he : e=storeSlotReadRef i slot
    · subst e
      obtain ⟨a,bs,hread⟩ := hread
      exact (storeReadFrame_no_old_read ho hmissing a bs hread).elim
    · simp [he]

theorem storeReadFrame_size (ho : X.tensorStores i=some o) (hmissing : o.effects.read slot=none)
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) : X.size L<(Y).size L := by
  apply recordStoreEffects_size_of_measure hg hi
  rw [ho]
  change o.effects.size<(o.readSlot slot value).effects.size
  rw [readSlot_size hmissing]
  omega

theorem storeReadFrame_full_not_done (hc : CopyOk o.spec o.effects)
    (hn : o.effects.readsDone=false) : o.effects.fullDone=false := by
  cases hf : o.effects.fullDone
  · rfl
  · have hh := (hc.complete hf).1
    rw [hn] at hh
    cases hh

theorem storeReadFrame_modelCausality (ho : X.tensorStores i=some o) (hc : CopyOk o.spec o.effects)
    (hn : o.effects.readsDone=false) (l : Loc) (e f : Ref) :
    modelCausality L Y l e f ↔ modelCausality L X l e f := by
  have hnF := storeReadFrame_full_not_done hc hn
  apply storeByteFrame_modelCausality
  · simp [ho,hn]
  · simp [ho,hnF]
  · exact hn
  · exact hnF
  · exact storeReadFrame_thread_rf (X:=X) (i:=i) (o:=o) (slot:=slot) (value:=value) (source:=source)

/-- An unfinished source read has no outgoing visibility edge, even as an
intent-only endpoint before its byte is recorded. -/
theorem storeRead_no_vis_from {X : Execution} {i : EvId}
    {outer : Nat} {d : TensorDescriptor.Descriptor outer} {slot : TensorTransfer.Slot d}
    (hnR : (X.tensorStores i).any (fun old => old.effects.readsDone)=false)
    {l : Loc} {target : Ref} : ¬modelCausality L X l (storeSlotReadRef i slot) target := by
  -- A group wait waits for the read completion of a tensor store, which is absent; the store
  -- bytes notify no mbarrier.
  have hgroup : ∀ (k : GroupWait), (∃ pc addr s, X.get i = some ⟨pc, .tensorStore addr s⟩) →
      (∀ q ∈ GroupWaitStages X i k, X.AsyncPresent i q) → False := by
    rintro k ⟨pc, addr, s, hg⟩ hall
    refine store_unfinished_no_readDone hnR (hall .readsDone ?_)
    unfold GroupWaitStages
    rw [hg]
    rcases k with ⟨_ | _ | _⟩ | _ <;> simp
  have hissue : ∀ {l : Loc}, AsyncCovers X i (.read (.store slot.1.val slot.2.1.val
      slot.2.2.val)) l → ∃ pc addr s, X.get i = some ⟨pc, .tensorStore addr s⟩ := by
    rintro l ⟨a, w, ⟨-, s, addr, ⟨pc, hg⟩, -⟩, -⟩
    exact ⟨pc, addr, s, hg⟩
  intro hv
  unfold storeSlotReadRef at hv
  cases target with
  | thread w =>
    obtain ⟨hc,waiter,hfinish,_⟩ := hv
    rcases hfinish with ⟨k,-,-,hall⟩ | ⟨ws,⟨n,m,hN,-⟩,-⟩
    · exact hgroup k (hissue hc) hall
    · exact hN
  | async j p =>
    obtain ⟨next,hedge⟩ := hv.2.first
    rcases hedge.2.2 with ⟨w,⟨k,-,-,hall⟩ | ⟨ws,⟨n,m,hN,-⟩,-⟩,_⟩ | ⟨w,⟨-,-,hall⟩,_⟩
    · exact hgroup k (hissue hedge.1) hall
    · exact hN
    · exact hgroup _ (hissue hedge.1) hall

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorStore MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {source : Option Ref}
local notation "Y" => X.recordStoreRead i o slot value source

private theorem storeReadFrame_byteCausality (ho : X.tensorStores i=some o)
    (hc : CopyOk o.spec o.effects) (hn : o.effects.readsDone=false)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (storeReadFrame_modelCausality ho hc hn l e f).mp) (fun h => h)

theorem storeReadWaiting_present_other (ho : X.tensorStores i=some o) {j : EvId} {p : Part}
    (hne : Ref.async j p≠storeSlotReadRef i slot) : (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  case readStore x y k =>
    by_cases hj : j=i
    · subst j
      have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
        rintro ⟨rfl,rfl,rfl⟩
        exact hne rfl
      simp only [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rw [readSlot_readByte_other hcoords]
    · simp only [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
        ite_eq_right hj]
  all_goals
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
        ite_eq_right hj]

theorem storeReadWaiting_refPresent_other (ho : X.tensorStores i=some o) {e : Ref}
    (hne : e≠storeSlotReadRef i slot) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p => exact storeReadWaiting_present_other ho hne

theorem storeReadWaiting_slot_unwritten (hc : CopyOk o.spec o.effects)
    (hmissing : o.effects.read slot=none) : o.effects.write slot=none := by
  cases hw : o.effects.write slot with
  | none => rfl
  | some byte =>
    obtain ⟨_,old,hread,_⟩ := hc.writes slot byte hw
    rw [hmissing] at hread
    cases hread

theorem storeReadWaiting_write_absent (ho : X.tensorStores i=some o)
    (hc : CopyOk o.spec o.effects) (hmissing : o.effects.read slot=none) :
    ¬(Y).AsyncPresent i (.write (.store slot.1.val slot.2.1.val slot.2.2.val)) := by
  have _ := ho
  have hw := storeReadWaiting_slot_unwritten hc hmissing
  simp [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
    TensorStore.writeByte,TensorStore.Observation.readSlot,TensorCopy.slotAt_self,hw]

theorem storeReadWaiting_readDone_absent (ho : X.tensorStores i=some o)
    (hn : o.effects.readsDone=false) : ¬(Y).AsyncPresent i .readsDone := by
  have _ := ho
  simp [Execution.AsyncPresent,Execution.recordStoreRead,Execution.recordStoreEffects,
    TensorStore.Observation.readSlot,hn]
theorem storeReadWaiting_read_absent (ho : X.tensorStores i=some o)
    (hmissing : o.effects.read slot=none) :
    ¬X.AsyncPresent i (.read (.store slot.1.val slot.2.1.val slot.2.2.val)) := by
  rintro ⟨old,hobs,hread⟩
  have heq : o=old := Option.some.inj (ho.symm.trans hobs)
  subst old
  rw [readByte_slot,hmissing] at hread
  cases hread

/-- The new store read starts no stage edge: its write and the read completion are absent. -/
theorem storeReadWaiting_no_edge (ho : X.tensorStores i=some o)
    (hc : CopyOk o.spec o.effects) (hmissing : o.effects.read slot=none)
    (hn : o.effects.readsDone=false) (f : Ref) :
    ¬StageEdge Y (storeSlotReadRef i slot) f := by
  intro ha
  unfold storeSlotReadRef at ha
  cases f with
  | thread j => exact ha
  | async j p =>
    cases p <;> try exact ha
    case writeStore x y k =>
      obtain ⟨he,hs,_,hw⟩ := ha
      cases he
      cases hs
      exact storeReadWaiting_write_absent ho hc hmissing hw
    case readsDone =>
      obtain ⟨he,_,hdone⟩ := ha
      cases he
      exact storeReadWaiting_readDone_absent ho hn hdone
    all_goals
      obtain ⟨-, hm, -⟩ := ha
      cases hm

/-- The new store read stage and the returns of the waits it witnesses form a sink; outside them
every order relation is old. -/
theorem storeReadWaiting_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o) (hc : CopyOk o.spec o.effects)
    (hmissing : o.effects.read slot=none) (hn : o.effects.readsDone=false) :
    SinkFrame L K A X Y (CompletionNodes L Y (· = storeSlotReadRef i slot)) :=
  sinkFrame_effect hX (· = storeSlotReadRef i slot) (fun _ h => by cases h)
    (fun _ _ he => by cases he; exact storeReadWaiting_read_absent ho hmissing)
    (fun _ he h => (storeReadWaiting_refPresent_other ho he).mp h)
    (recordStoreEffects_needs hX.tma.2.2.1) (fun _ _ => ite_eq_right (by simp [storeSlotReadRef]))
    (fun _ _ _ _ h => h)
    (fun _ f he => by subst he; exact storeReadWaiting_no_edge ho hc hmissing hn f)
    (fun m r hr he => by
      have hm := ((hX.tma.2.2.1 m).2.1 r hr).1
      rw [he] at hm
      simp [objectAction,storeSlotReadRef] at hm)

theorem storeReadWaiting_order {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o)
    (hmissing : o.effects.read slot=none)
    (hn : o.effects.readsDone=false) : OrderOk L K A Y :=
  (storeReadWaiting_sinkFrame hX ho (hX.store i o ho).2.2 hmissing hn).orderOk hX.orderOk

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorStore
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {w : Ref}
local notation "Y" => X.recordStoreRead i o slot value (some w)

theorem storeReadFrame_rf_of_write (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o) (hmissing : o.effects.read slot=none)
    {dst : Acc} {written : List Byte} (hw : X.MemWrites w dst written)
    (hcover : dst.Covers (o.spec.sharedLoc slot))
    (hvalue : wbyte dst written (o.spec.sharedLoc slot)=some value) : RfWf mem0 Y := by
  have _ := hmissing
  intro e a bs he
  by_cases href : e=storeSlotReadRef i slot
  · subst e
    obtain ⟨hloc,hsize,hbs⟩ := storeReadFrame_reads_self he
    refine ⟨by simp [hbs,hsize],?_⟩
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    have hrf : (Y).rf (storeSlotReadRef i slot) 0=some w := by
      simp [Execution.recordStoreRead,Execution.recordStoreEffects]
    rw [hrf]
    change ∃footprint bytes,(Y).MemWrites w footprint bytes ∧
      footprint.Covers (a.loc.at 0) ∧ bs[0]?=some (wbyte footprint bytes (a.loc.at 0))
    refine ⟨dst,written,(storeReadFrame_writes ho _ _ _).mpr hw,?_,?_⟩
    · simpa only [hloc,Loc.at,Nat.add_zero] using hcover
    · simp only [hbs,List.getElem?_cons_zero,hloc,Loc.at,Nat.add_zero,hvalue]
  · have hold := (storeReadFrame_reads_other ho href a bs).mp he
    obtain ⟨hlen,hvalues⟩ := hX.rf e a bs hold
    refine ⟨hlen,?_⟩
    intro k hk
    have hv := hvalues k hk
    cases hsrc : X.rf e k with
    | none =>
      rw [hsrc] at hv
      simp only [Execution.recordStoreRead,Execution.recordStoreEffects,ite_eq_right href,hsrc]
      exact hv
    | some source =>
      rw [hsrc] at hv
      obtain ⟨footprint,bytes,hwrite,hcov,hbyte⟩ := hv
      simp only [Execution.recordStoreRead,Execution.recordStoreEffects,ite_eq_right href,hsrc]
      exact ⟨footprint,bytes,(storeReadFrame_writes ho _ _ _).mpr hwrite,hcov,hbyte⟩

theorem storeReadFrame_noFuture (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o) (hn : o.effects.readsDone=false)
    (hmissing : o.effects.read slot=none) : NoFuture L Y := by
  have _ := hmissing
  have hc := (hX.store i o ho).2.2
  intro e a bs k source he hk hr hv
  by_cases href : e=storeSlotReadRef i slot
  · subst e
    obtain ⟨first, hfirst⟩ := hv.starts
    exact storeRead_no_vis_from (by simp [Execution.recordStoreRead,Execution.recordStoreEffects,
        TensorStore.Observation.readSlot,hn]) (target := first) hfirst
  · have hold := (storeReadFrame_reads_other ho href a bs).mp he
    have hrs : X.rf e k=some source := by
      simpa only [Execution.recordStoreRead,Execution.recordStoreEffects,ite_eq_right href] using hr
    exact hX.noFuture e a bs k source hold hk hrs
        (storeReadFrame_byteCausality ho hc hn hv)

/-- The sole dynamic coherence obligation for the new source byte. It concerns
actual covering writers and the pending read intent, with no chosen numerical
payload or whole-execution safety assumption. -/
theorem storeReadFrame_hidden_of_latest (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i=some o) (hn : o.effects.readsDone=false)
    (hmissing : o.effects.read slot=none)
    (hlatest : ∀other footprint bytes,X.MemWrites other footprint bytes →
      footprint.Covers (o.spec.sharedLoc slot) →
      ByteCausality L X (o.spec.sharedLoc slot) other (storeSlotReadRef i slot) →
      ¬ByteCausality L X (o.spec.sharedLoc slot) w other) : Hidden L Y := by
  have _ := hmissing
  have hc := (hX.store i o ho).2.2
  intro e a bs k other footprint bytes he hk hwrite hcov hvis
  have hwold := (storeReadFrame_writes ho _ _ _).mp hwrite
  by_cases href : e=storeSlotReadRef i slot
  · subst e
    obtain ⟨hloc,hsize,_⟩ := storeReadFrame_reads_self he
    have hk0 : k=0 := by omega
    subst k
    have hcov' : footprint.Covers (o.spec.sharedLoc slot) := by
      simpa only [hloc,Loc.at,Nat.add_zero] using hcov
    have hvisible : ByteCausality L X (o.spec.sharedLoc slot) other (storeSlotReadRef i slot) := by
      simpa only [hloc,Loc.at,Nat.add_zero] using
        storeReadFrame_byteCausality ho hc hn hvis
    have hrf : (Y).rf (storeSlotReadRef i slot) 0=some w := by
      simp [Execution.recordStoreRead,Execution.recordStoreEffects]
    rw [hrf]
    change ¬ByteCausality L Y (a.loc.at 0) w other
    intro hbad
    apply hlatest other footprint bytes hwold hcov' hvisible
    simpa only [hloc, Loc.at, Nat.add_zero] using
        storeReadFrame_byteCausality ho hc hn hbad
  · have hold := (storeReadFrame_reads_other ho href a bs).mp he
    have hvisold := storeReadFrame_byteCausality ho hc hn hvis
    have hh := hX.hidden e a bs k other footprint bytes hold hk hwold hcov hvisold
    cases hsrc : X.rf e k with
    | none => simp only [hsrc] at hh
    | some source =>
      rw [hsrc] at hh
      simp only [Execution.recordStoreRead,Execution.recordStoreEffects,ite_eq_right href,hsrc]
      exact fun hbad => hh (storeReadFrame_byteCausality ho hc hn hbad)

end
end PTX
end
