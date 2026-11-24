-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistentRead
public import Lemmas.TensorStore.TensorStoreCompleteConsistentByteVisibility
public import Lemmas.Order.VisibilityFrame

@[expose] public section

section
namespace PTX.TensorStore
noncomputable section

def Observation.writeSlot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor)
    (value : Byte) : Observation :=
  ⟨o.spec,{o.effects with write:=Function.update o.effects.write slot (some value)}⟩

theorem writeSlot_copyOk {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} {loc : Loc} (hc : CopyOk o.spec o.effects) (hred : o.spec.reduce=none)
    (hd : destination o.spec slot=some loc) (hr : o.effects.read slot=some value) :
    CopyOk (o.writeSlot slot value).spec (o.writeSlot slot value).effects := by
  constructor
  · intro (q : TensorTransfer.Slot o.spec.descriptor) byte hw
    by_cases hq : q=slot
    · subst q
      have hb : value=byte := by simpa [Observation.writeSlot] using hw
      subst byte
      exact ⟨⟨loc,hd⟩,value,hr,fun _ => rfl⟩
    · exact hc.writes q byte (by simpa [Observation.writeSlot,Function.update_of_ne hq] using hw)
  · exact hc.readsComplete
  · intro hf
    obtain ⟨hreads,hwrites⟩ := hc.complete hf
    refine ⟨hreads,?_⟩
    intro (q : TensorTransfer.Slot o.spec.descriptor) dst hdst
    by_cases hq : q=slot
    · subst q
      exact ⟨value,by simp [Observation.writeSlot]⟩
    · obtain ⟨b,hb⟩ := hwrites q dst hdst
      exact ⟨b,by simpa [Observation.writeSlot,Function.update_of_ne hq] using hb⟩
  · intro _ _ _ hr'
    change o.spec.reduce.isSome=true at hr'
    rw [hred] at hr'
    cases hr'
  · intro q b hb
    obtain ⟨hr',-⟩ := hc.old q b hb
    rw [hred] at hr'
    cases hr'

theorem writeSlot_extends {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hn : o.effects.write slot=none) : o.Extends (o.writeSlot slot value) := by
  refine ⟨rfl,fun _ _ h => h,?_,fun h => h,fun h => h,fun _ => rfl,fun _ _ h => h⟩
  intro (q : TensorTransfer.Slot o.spec.descriptor) byte hw
  by_cases hq : q=slot
  · subst q
    rw [hn] at hw
    cases hw
  · simpa [Observation.writeSlot,Function.update_of_ne hq] using hw

theorem writeSlot_size {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hn : o.effects.write slot=none) :
    (o.writeSlot slot value).effects.size=o.effects.size+1 := by
  have hs : (o.writeSlot slot value).effects.writeSlots=insert slot o.effects.writeSlots := by
    change (Finset.univ.filter fun r : TensorTransfer.Slot o.spec.descriptor =>
      (Function.update o.effects.write slot (some value) r).isSome)=insert slot o.effects.writeSlots
    ext q
    by_cases hq : q=slot
    · subst q
      simp [Effects.writeSlots]
    · simp [Effects.writeSlots,hq]
  have hnot : slot∉o.effects.writeSlots := by simp [Effects.writeSlots,hn]
  have hcard : (o.writeSlot slot value).effects.writeSlots.card=o.effects.writeSlots.card+1 := by
    rw [hs]
    exact Finset.card_insert_of_notMem hnot
  unfold Effects.size
  rw [hcard]
  change o.effects.readSlots.card+(o.effects.writeSlots.card+1)+
      (if o.effects.readsDone then 1 else 0)+(if o.effects.fullDone then 1 else 0)=
    o.effects.readSlots.card+o.effects.writeSlots.card+
      (if o.effects.readsDone then 1 else 0)+(if o.effects.fullDone then 1 else 0)+1
  omega

theorem writeSlot_writeByte_other {o : Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {x y k : Nat}
    (hne : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val)) :
    writeByte (o.writeSlot slot value) x y k=writeByte o x y k := by
  unfold writeByte
  cases hq : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [Observation.writeSlot,hq]
  | some q =>
    have hqs : q≠slot := by
      intro he
      subst q
      have hh := TensorCopy.slotAt_coordinates hq
      exact hne ⟨hh.1.symm,hh.2.1.symm,hh.2.2.symm⟩
    simp [Observation.writeSlot,hq,Function.update_of_ne hqs]

theorem missing_required_before_fullDone {o : Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {loc : Loc}
    (hc : CopyOk o.spec o.effects) (hd : destination o.spec slot=some loc)
    (hn : o.effects.write slot=none) : o.effects.fullDone=false := by
  cases hf : o.effects.fullDone
  · rfl
  · obtain ⟨b,hb⟩ := (hc.complete hf).2 slot loc hd
    rw [hn] at hb
    cases hb

end
end PTX.TensorStore
end

section
namespace PTX
open AsyncCopy TensorStore
noncomputable section

def storeSlotWriteRef (i : EvId) {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) : Ref :=
  .async i (.write (.store slot.1.val slot.2.1.val slot.2.2.val))

def Execution.recordStoreWrite (X : Execution) (i : EvId) (o : TensorStore.Observation)
    (slot : TensorTransfer.Slot o.spec.descriptor) (value : Byte) : Execution :=
  X.recordStoreEffects i (o.writeSlot slot value) X.rf

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte}
local notation "Y" => X.recordStoreWrite i o slot value

theorem storeWriteFrame_reads (ho : X.tensorStores i=some o) (e : Ref) (a : Acc)
    (bs : List (Option Byte)) : (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readStore x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemReads,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemReads,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl
    case oldStore x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemReads,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemReads,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem storeWriteFrame_writes_other (ho : X.tensorStores i=some o) {e : Ref}
    (hne : e≠storeSlotWriteRef i slot) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeStore x y k =>
      by_cases hj : j=i
      · subst j
        have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
          rintro ⟨rfl,rfl,rfl⟩
          exact hne rfl
        simp only [Execution.MemWrites,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rw [writeSlot_writeByte_other hcoords]
        rfl
      · simp only [Execution.MemWrites,Execution.recordStoreWrite,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem storeWriteFrame_present_other (ho : X.tensorStores i=some o) {j : EvId} {p : Part}
    (hne : Ref.async j p≠storeSlotWriteRef i slot) : (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  case writeStore x y k =>
    by_cases hj : j=i
    · subst j
      have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
        rintro ⟨rfl,rfl,rfl⟩
        exact hne rfl
      simp only [Execution.AsyncPresent,Execution.recordStoreWrite,Execution.recordStoreEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rw [writeSlot_writeByte_other hcoords]
    · simp only [Execution.AsyncPresent,Execution.recordStoreWrite,Execution.recordStoreEffects,
        ite_eq_right hj]
  all_goals
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordStoreWrite,Execution.recordStoreEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordStoreWrite,Execution.recordStoreEffects,
        ite_eq_right hj]

theorem storeWriteFrame_refPresent_other (ho : X.tensorStores i=some o) {e : Ref}
    (hne : e≠storeSlotWriteRef i slot) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p => exact storeWriteFrame_present_other ho hne

theorem storeWriteFrame_readDone (ho : X.tensorStores i=some o) (j : EvId) :
    (Y).AsyncPresent j .readsDone ↔ X.AsyncPresent j .readsDone := by
  exact storeWriteFrame_present_other ho (by intro h; cases h)

theorem storeWriteFrame_fullDone (ho : X.tensorStores i=some o) (j : EvId) :
    (Y).AsyncPresent j .fullDone ↔ X.AsyncPresent j .fullDone := by
  exact storeWriteFrame_present_other ho (by intro h; cases h)

theorem storeWriteFrame_groupPresent (ho : X.tensorStores i=some o) (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages Y j k, (Y).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl
    · exact storeWriteFrame_readDone ho j
    · exact storeWriteFrame_fullDone ho j
    · exact Iff.rfl
    · exact Iff.rfl

theorem storeWriteFrame_finished (ho : X.tensorStores i=some o) (j : EvId) (p : Part) (w : EvId) :
    AsyncFinished L Y j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
    storeWriteFrame_groupPresent ho j k) Iff.rfl

theorem storeWriteFrame_onlyFinished (ho : X.tensorStores i=some o) (j : EvId)
    (p : Part) (w : EvId) :
    AsyncOnlyFinished Y j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => storeWriteFrame_groupPresent ho j _

theorem storeWriteFrame_no_fullDone (hn : o.effects.fullDone=false) :
    ¬(Y).AsyncPresent i .fullDone :=
  store_unfinished_no_fullDone (by simp [Execution.recordStoreWrite,Execution.recordStoreEffects,
    TensorStore.Observation.writeSlot,hn])

/-- Before the full completion of the store, no wait observes the completion of its write: a group
wait that sees the write waits for the full completion, and the write notifies no mbarrier. -/
theorem storeWriteFrame_not_finished (hn : o.effects.fullDone=false) {l : Loc} {w : EvId}
    (hc : AsyncCovers Y i (.write (.store slot.1.val slot.2.1.val slot.2.2.val)) l) :
    ¬AsyncFinished L Y i (.write (.store slot.1.val slot.2.1.val slot.2.2.val)) w ∧
      ¬AsyncOnlyFinished Y i (.write (.store slot.1.val slot.2.1.val slot.2.2.val)) w := by
  obtain ⟨a, w', ⟨-, s, addr, ⟨pc, hg⟩, -⟩, -⟩ := hc
  have hstage : ∀ k, GroupWaitVisible k (.write (.store slot.1.val slot.2.1.val slot.2.2.val))
      = true → Part.fullDone ∈ GroupWaitStages Y i k := by
    intro k hv
    unfold GroupWaitStages
    rw [hg]
    rcases k with ⟨_ | _ | _⟩ | _ <;> simp_all [GroupWaitVisible]
  refine ⟨?_, ?_⟩
  · rintro (⟨k, hv, -, hall⟩ | ⟨ws, ⟨n, m, hN, -⟩, -⟩)
    · exact storeWriteFrame_no_fullDone hn (hall _ (hstage k hv))
    · exact hN
  · rintro ⟨hv, -, hall⟩
    refine storeWriteFrame_no_fullDone hn (hall _ ?_)
    unfold GroupWaitStages
    rw [hg]
    simp

theorem storeWriteFrame_no_before (hn : o.effects.fullDone=false) {l : Loc} {b : EvId × Part} :
    ¬AsyncBefore L Y l (i,.write (.store slot.1.val slot.2.1.val slot.2.2.val)) b := by
  rintro ⟨hc,_,⟨w,hf,_⟩ | ⟨w,hf,_⟩⟩
  · exact (storeWriteFrame_not_finished hn hc).1 hf
  · exact (storeWriteFrame_not_finished (L := L) hn hc).2 hf

theorem storeWriteFrame_no_vis_from (hn : o.effects.fullDone=false) {l : Loc} {target : Ref} :
    ¬modelCausality L Y l (storeSlotWriteRef i slot) target := by
  cases target with
  | thread j =>
    rintro ⟨hc,w,hf,_⟩
    exact (storeWriteFrame_not_finished hn hc).1 hf
  | async j p =>
    intro h
    obtain ⟨b,hb⟩ := h.2.first
    exact storeWriteFrame_no_before hn hb

theorem storeWriteFrame_modelCausality (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [modelCausality,storeWriteFrame_finished ho]
    rfl
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges
      (fun a b => by simp only [AsyncBefore,storeWriteFrame_finished ho,
        storeWriteFrame_onlyFinished ho]; rfl)
    intro a b hedge
    apply storeWriteFrame_present_other ho
    intro he
    have hparts := Ref.async.inj he
    have ha : a=(i,.write (.store slot.1.val slot.2.1.val slot.2.2.val)) :=
      Prod.ext hparts.1 hparts.2
    rw [ha] at hedge
    exact storeWriteFrame_no_before hn hedge

theorem storeWriteFrame_byteCausality (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (storeWriteFrame_modelCausality ho hn l e f).mp) (fun h => h)

theorem storeWriteFrame_le (ho : X.tensorStores i=some o) (hn : o.effects.write slot=none) :
    X.le Y := by
  apply Execution.le_recordStoreEffects
  · intro old hold
    have heq := Option.some.inj (ho.symm.trans hold)
    subst old
    exact writeSlot_extends hn
  · intros; rfl

theorem storeWriteFrame_rf {mem0 : Mem0} (hX : RfWf mem0 X)
    (ho : X.tensorStores i=some o) (hn : o.effects.write slot=none) : RfWf mem0 Y := by
  intro e a bs he
  obtain ⟨hlen,hvalues⟩ := hX e a bs ((storeWriteFrame_reads ho e a bs).mp he)
  refine ⟨hlen,?_⟩
  intro k hk
  have hv := hvalues k hk
  change match X.rf e k with | none => _ | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hv ⊢; exact hv
  | some w =>
    rw [hsrc] at hv
    obtain ⟨dst,bytes,hw,hcover,hval⟩ := hv
    exact ⟨dst,bytes,Execution.le_memWrites (storeWriteFrame_le ho hn) hw,hcover,hval⟩

theorem storeWriteFrame_hidden (hX : Hidden L X) (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false) : Hidden L Y := by
  intro e a bs k w dst bytes he hk hw hc hv
  by_cases hwi : w=storeSlotWriteRef i slot
  · subst w
    obtain ⟨first, hfirst⟩ := hv.starts
    exact (storeWriteFrame_no_vis_from hn (target := first) hfirst).elim
  · have hold := hX e a bs k w dst bytes ((storeWriteFrame_reads ho e a bs).mp he) hk
      ((storeWriteFrame_writes_other ho hwi dst bytes).mp hw) hc
      (storeWriteFrame_byteCausality ho hn hv)
    change match X.rf e k with | none => False | some w' => _
    cases hsrc : X.rf e k with
    | none => simp only [hsrc] at hold
    | some w' =>
      simp only [hsrc] at hold
      exact fun hh => hold (storeWriteFrame_byteCausality ho hn hh)

end
end PTX
end
