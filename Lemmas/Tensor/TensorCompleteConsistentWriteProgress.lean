-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Execution.EffectFrame

@[expose] public section

section
namespace PTX.TensorCopy
noncomputable section

def Observation.writeSlot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor)
    (value : Content) : Observation :=
  ⟨o.spec,{o.effects with write := Function.update o.effects.write slot (some value)}⟩

def WriteValue (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor)
    (value : Content) : Prop :=
  match source o.spec slot with
  | .global _ => ∃byte,o.effects.read slot=some byte ∧ value=.copied byte
  | .fill mode format byte => value=.filled mode format byte

theorem writeSlot_copyOk {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Content} (hc : CopyOk o.spec o.effects) (hn : o.effects.notified=false)
    (hv : WriteValue o slot value) :
    CopyOk (o.writeSlot slot value).spec (o.writeSlot slot value).effects := by
  constructor
  · exact hc.reads
  · intro (q : TensorTransfer.Slot o.spec.descriptor) content hw
    by_cases hq : q=slot
    · subst q
      have he : value=content := by simpa [Observation.writeSlot] using hw
      subst content
      exact hv
    · apply hc.writes q content
      simpa only [Observation.writeSlot,Function.update_of_ne hq] using hw
  · intro h
    change o.effects.notified=true at h
    rw [hn] at h
    cases h

theorem writeSlot_extends {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Content} (hm : o.effects.write slot=none) : o.Extends (o.writeSlot slot value) := by
  refine ⟨rfl,fun _ _ h => h,?_,fun h => h⟩
  intro (q : TensorTransfer.Slot o.spec.descriptor) byte hw
  by_cases hq : q=slot
  · subst q
    rw [hm] at hw
    cases hw
  · simpa only [Observation.writeSlot,Function.update_of_ne hq] using hw

theorem writeSlot_size {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Content} (hm : o.effects.write slot=none) :
    (o.writeSlot slot value).effects.size=o.effects.size+1 := by
  have hs : (o.writeSlot slot value).effects.writeSlots=insert slot o.effects.writeSlots := by
    change (Finset.univ.filter fun r : TensorTransfer.Slot o.spec.descriptor =>
      (Function.update o.effects.write slot (some value) r).isSome)=insert slot o.effects.writeSlots
    ext q
    by_cases hq : q=slot
    · subst q
      simp [Effects.writeSlots]
    · simp [Effects.writeSlots,hq]
  have hn : slot∉o.effects.writeSlots := by simp [Effects.writeSlots,hm]
  have hcard : (o.writeSlot slot value).effects.writeSlots.card=o.effects.writeSlots.card+1 := by
    rw [hs]
    exact Finset.card_insert_of_notMem hn
  unfold Effects.size
  rw [hcard]
  change o.effects.readSlots.card+(o.effects.writeSlots.card+1)+
      (if o.effects.notified then 1 else 0)=
    o.effects.readSlots.card+o.effects.writeSlots.card+
      (if o.effects.notified then 1 else 0)+1
  omega

theorem writeSlot_writeByte_other {o : Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content} {x y k : Nat}
    (hne : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val)) :
    writeByte (o.writeSlot slot value) x y k=writeByte o x y k := by
  unfold writeByte
  cases hq : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [Observation.writeSlot,hq]
  | some q =>
    have hqs : q≠slot := by
      intro he
      subst q
      have hh := slotAt_coordinates hq
      exact hne ⟨hh.1.symm,hh.2.1.symm,hh.2.2.symm⟩
    simp [Observation.writeSlot,hq,Function.update_of_ne hqs]

end
end PTX.TensorCopy
end

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section

def tensorSlotWriteRef (i : EvId) {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) : Ref :=
  .async i (.write (.load slot.1.val slot.2.1.val slot.2.2.val))

def Execution.recordTensorWrite (X : Execution) (i : EvId) (o : TensorCopy.Observation)
    (slot : TensorTransfer.Slot o.spec.descriptor) (value : Content) : Execution :=
  X.recordTensorEffects i (o.writeSlot slot value)
    X.rf

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content}
local notation "Y" => X.recordTensorWrite i o slot value

theorem tensorWriteFrame_no_old_write (ho : X.tensor i=some o)
    (hm : o.effects.write slot=none) (a : Acc) (bs : List Byte) :
    ¬X.MemWrites (tensorSlotWriteRef i slot) a bs := by
  rintro ⟨old,address,b,hobs,hissue,hloc,hread,_,_⟩
  have heq : o=old := Option.some.inj (ho.symm.trans hobs)
  subst old
  simp [writeByte,slotAt_self,hm] at hread

theorem tensorWriteFrame_writes_other (ho : X.tensor i=some o) {e : Ref}
    (hne : e≠tensorSlotWriteRef i slot) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeLoad x y k =>
      by_cases hj : j=i
      · subst j
        have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
          rintro ⟨rfl,rfl,rfl⟩
          exact hne rfl
        simp only [Execution.MemWrites,Execution.recordTensorWrite,Execution.recordTensorEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rw [writeSlot_writeByte_other hcoords]
        rfl
      · simp only [Execution.MemWrites,Execution.recordTensorWrite,Execution.recordTensorEffects,
          ite_eq_right hj]
        rfl

theorem tensorWriteFrame_reads (ho : X.tensor i=some o) (e : Ref) (a : Acc)
    (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemReads,Execution.recordTensorWrite,Execution.recordTensorEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemReads,Execution.recordTensorWrite,Execution.recordTensorEffects,
          ite_eq_right hj]
        rfl

theorem tensorWriteFrame_writes_mono (ho : X.tensor i=some o)
    (hm : o.effects.write slot=none) {e : Ref} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites e a bs) : (Y).MemWrites e a bs := by
  by_cases he : e=tensorSlotWriteRef i slot
  · subst e
    exact (tensorWriteFrame_no_old_write ho hm a bs hw).elim
  · exact (tensorWriteFrame_writes_other ho he a bs).mpr hw

theorem tensorWriteFrame_modelCausality (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f :=
  tensorByteFrame_modelCausality (X := X) (i := i) (o := o.writeSlot slot value)
    (rf := X.rf) (by simp [ho,hn]) hn (by intros; rfl) l e f

private theorem tensorWriteFrame_byteCausality (ho : X.tensor i=some o)
    (hn : o.effects.notified=false)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (tensorWriteFrame_modelCausality ho hn l e f).mp) (fun h => h)

theorem tensorWriteFrame_le (ho : X.tensor i=some o) (hm : o.effects.write slot=none) :
    X.le Y := by
  apply Execution.le_recordTensorEffects
  · intro old hold
    have heq := Option.some.inj (ho.symm.trans hold)
    subst old
    exact writeSlot_extends hm
  · intros; rfl

theorem tensorWriteFrame_size (ho : X.tensor i=some o) (hm : o.effects.write slot=none)
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) : X.size L<(Y).size L := by
  apply recordTensorEffects_size_of_measure hg hi
  rw [ho]
  change o.effects.size<(o.writeSlot slot value).effects.size
  rw [writeSlot_size hm]
  omega
theorem tensorWriteFrame_present_other (ho : X.tensor i=some o) {j : EvId} {p : Part}
    (hne : Ref.async j p≠tensorSlotWriteRef i slot) :
    (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  case readLoad x y k =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ite_eq_right hj]
  case writeLoad x y k =>
    by_cases hj : j=i
    · subst j
      have hq (q : TensorTransfer.Slot o.spec.descriptor)
          (hs : TensorTransfer.slotAt o.spec.descriptor x y k=some q) : q≠slot := by
        intro he
        subst q
        obtain ⟨hx,hy,hk⟩ := slotAt_coordinates hs
        apply hne
        simp [tensorSlotWriteRef,←hx,←hy,←hk]
      simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
      constructor <;> rintro ⟨q,hs,c,hw⟩ <;>
        exact ⟨q,hs,c,by simpa only [Observation.writeSlot,
          Function.update_of_ne (hq q hs)] using hw⟩
    · simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ite_eq_right hj]
  case notifyLoad =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorWrite,Execution.recordTensorEffects,
        ite_eq_right hj]

theorem tensorWriteFrame_refPresent_other (ho : X.tensor i=some o) {e : Ref}
    (hne : e≠tensorSlotWriteRef i slot) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p => exact tensorWriteFrame_present_other ho hne


end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content}
local notation "Y" => X.recordTensorWrite i o slot value

theorem tensorWriteMemory_rf (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hm : o.effects.write slot=none) : RfWf mem0 Y := by
  intro e a bs he
  have oldRead := (tensorWriteFrame_reads ho e a bs).mp he
  obtain ⟨hlen,hr⟩ := hX.rf e a bs oldRead
  refine ⟨hlen,?_⟩
  intro k hk
  have hs := hr k hk
  change match X.rf e k with | none => _ | some w => _
  cases hsrc : X.rf e k with
  | none =>
    rw [hsrc] at hs
    exact hs
  | some w =>
    rw [hsrc] at hs
    obtain ⟨dst,bytes,hw,hcover,hbyte⟩ := hs
    exact ⟨dst,bytes,tensorWriteFrame_writes_mono ho hm hw,hcover,hbyte⟩

theorem tensorWriteMemory_noFuture (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false) : NoFuture L Y := by
  intro e a bs k w he hk hr hvis
  exact hX.noFuture e a bs k w ((tensorWriteFrame_reads ho e a bs).mp he) hk hr
    (tensorWriteFrame_byteCausality ho hn hvis)

theorem tensorWriteMemory_unpublished (ho : X.tensor i=some o)
    (hn : o.effects.notified=false) (l : Loc) (e : Ref) :
    ¬modelCausality L X l (tensorSlotWriteRef i slot) e := by
  have hnot (w : EvId) (ws : MbarScope) : ¬AsyncObserved X i (.notify .load) w true ws :=
    tensor_unnotified_not_observed (by simp [ho,hn])
  intro h
  cases e with
  | thread j =>
    obtain ⟨-,w,hf,-⟩ := h
    rcases hf with ⟨k,hv,-⟩ | ⟨ws,hw,-⟩
    · exact absurd hv (by rcases k with ⟨_ | _ | _⟩ | _ <;> simp [GroupWaitVisible])
    · exact hnot _ ws hw
  | async j p =>
    obtain ⟨c,hfirst⟩ := AsyncChain.first h.2
    rcases hfirst.2.2 with ⟨w,⟨k,hv,-⟩ | ⟨ws,hw,-⟩,_⟩ | ⟨w,hw,_⟩
    · exact absurd hv (by rcases k with ⟨_ | _ | _⟩ | _ <;> simp [GroupWaitVisible])
    · exact hnot w ws hw
    · exact absurd hw.1 (by simp [GroupWaitVisible])

theorem tensorWriteMemory_hidden (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false) : Hidden L Y := by
  intro e a bs k w dst bytes he hk hw hcover hvis
  have oldVis := tensorWriteFrame_byteCausality ho hn hvis
  by_cases hid : w=tensorSlotWriteRef i slot
  · subst w
    obtain ⟨first, hfirst⟩ := oldVis.starts
    exact (tensorWriteMemory_unpublished ho hn _ first hfirst).elim
  · have oldWrite := (tensorWriteFrame_writes_other ho hid dst bytes).mp hw
    have hh := hX.hidden e a bs k w dst bytes
      ((tensorWriteFrame_reads ho e a bs).mp he) hk oldWrite hcover oldVis
    change match X.rf e k with | none => _ | some source => _
    cases hsrc : X.rf e k with
    | none => rw [hsrc] at hh; exact hh
    | some source =>
      rw [hsrc] at hh
      intro hbefore
      exact hh (tensorWriteFrame_byteCausality ho hn hbefore)

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content}
local notation "Y" => X.recordTensorWrite i o slot value

/-- The new write stage starts no stage edge: the notification of the load is absent. -/
theorem tensorWriteWaiting_no_edge (hn : o.effects.notified=false) (f : Ref) :
    ¬StageEdge Y (tensorSlotWriteRef i slot) f := by
  intro ha
  unfold tensorSlotWriteRef at ha
  cases f with
  | thread j => exact ha
  | async j p =>
    cases p <;> try exact ha
    all_goals try (have hmis := ha.2.1; simp [AsyncCopy.Part.target] at hmis; done)
    obtain ⟨he,_,_,hw⟩ := ha
    cases he
    obtain ⟨old,hobs,hnotified⟩ := hw
    have ht : (Y).tensor i=some (o.writeSlot slot value) := by
      simp [Execution.recordTensorWrite,Execution.recordTensorEffects]
    have heq := Option.some.inj (ht.symm.trans hobs)
    subst old
    change o.effects.notified=true at hnotified
    rw [hn] at hnotified
    cases hnotified

/-- The new write stage, when absent before, and the returns of the waits it witnesses form a
sink; outside them every order relation is old. -/
theorem tensorWriteWaiting_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o) (hn : o.effects.notified=false) :
    SinkFrame L K A X Y
      (CompletionNodes L Y (fun x => x = tensorSlotWriteRef i slot ∧ ¬ X.RefPresent x)) :=
  sinkFrame_effect hX (fun x => x = tensorSlotWriteRef i slot ∧ ¬ X.RefPresent x)
    (fun _ h => by cases h.1)
    (fun _ _ he => he.2)
    (fun e he h => by
      by_cases hw : e = tensorSlotWriteRef i slot
      · by_contra hx
        exact he ⟨hw, hx⟩
      · exact (tensorWriteFrame_refPresent_other ho hw).mp h)
    (recordTensorEffects_needs hX.tma.2.2.1 (by simp [ho,Observation.writeSlot]))
    (fun _ _ => rfl)
    (fun _ _ _ _ h => recordTensorEffects_asyncObserved (o := o.writeSlot slot value)
      (fun h => ⟨o,ho,rfl,h⟩) h)
    (fun _ f he => he.1 ▸ tensorWriteWaiting_no_edge hn f)
    (fun m r hr he => by
      have hm := ((hX.tma.2.2.1 m).2.1 r hr).1
      rw [he.1] at hm
      simp [objectAction,tensorSlotWriteRef] at hm)

theorem tensorWriteWaiting_order {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hn : o.effects.notified=false) : OrderOk L K A Y :=
  (tensorWriteWaiting_sinkFrame hX ho hn).orderOk hX.orderOk

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section

/-- Record one valid pending tensor write without changing reads or RF. -/
theorem tensor_write_counted_extension {L : Launch} {K : Kernel} {mem0 : Mem0}
    {A : List Assumption} (hA : ∀ a ∈ A, ∀ Z, a.wf L mem0 Z)
    {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hmissing : o.effects.write slot=none)
    (hv : TensorCopy.WriteValue o slot value) :
    ∃Y,Consistent L K A mem0 Y ∧
      X.le Y ∧ X.size L<Y.size L := by
  obtain ⟨⟨mapAddress,hi⟩,hcopy,hrouting,hvalid⟩ := hX.tensor i o ho
  have hg : i.1<L.threads := by
    by_contra hh
    have hempty := hX.outside i.1 (by omega)
    obtain ⟨pc,he⟩ := hi
    simp only [Execution.get,hempty,List.getElem?_nil] at he
    cases he
  have hindex : i.2<(X.tr i.1).length := len_of_get hi.choose_spec
  let Y := X.recordTensorWrite i o slot value
  have hconsistent : Consistent L K A mem0 Y := by
    apply consistent_recordTensorEffects (o := o.writeSlot slot value) hX ⟨mapAddress,hi⟩
      (writeSlot_copyOk hcopy hn hv) hrouting hvalid
      (by rw [ho]; rfl)
    · exact tensorWriteMemory_rf hX ho hmissing
    · exact tensorWriteWaiting_order hX ho hn
    · exact tensorWriteMemory_noFuture hX ho hn
    · exact tensorWriteMemory_hidden hX ho hn
    · intro e k
      rfl
    · intro _ _ _ _
      rfl
    · intro a ha
      exact hA a ha _
    · intro _ _ _
      rfl
  exact ⟨Y,hconsistent,tensorWriteFrame_le ho hmissing,tensorWriteFrame_size ho hmissing hg hindex⟩

end
end PTX
end
