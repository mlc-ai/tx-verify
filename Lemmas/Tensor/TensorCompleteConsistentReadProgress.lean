-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Execution.EffectFrame

@[expose] public section

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section

def tensorSlotReadRef (i : EvId) {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) : Ref :=
  .async i (.read (.load slot.1.val slot.2.1.val slot.2.2.val))

def Execution.recordTensorRead (X : Execution) (i : EvId) (o : TensorCopy.Observation)
    (slot : TensorTransfer.Slot o.spec.descriptor) (value : Byte) : Execution :=
  X.recordTensorEffects i (o.readSlot slot value)
    (fun e k => if e=tensorSlotReadRef i slot then none else X.rf e k)

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte}
local notation "Y" => X.recordTensorRead i o slot value

theorem tensorReadFrame_no_old_read (ho : X.tensor i=some o)
    (hmissing : o.effects.read slot=none) (a : Acc) (bs : List (Option Byte)) :
    ¬X.MemReads (tensorSlotReadRef i slot) a bs := by
  rintro ⟨old,address,b,hobs,hissue,hloc,hread,_,_⟩
  have heq : o=old := Option.some.inj (ho.symm.trans hobs)
  subst old
  rw [readByte_slot,hmissing] at hread
  cases hread

theorem tensorReadFrame_reads_other (ho : X.tensor i=some o) {e : Ref}
    (hne : e≠tensorSlotReadRef i slot) (a : Acc) (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readLoad x y k =>
      by_cases hj : j=i
      · subst j
        have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
          rintro ⟨rfl,rfl,rfl⟩
          exact hne rfl
        simp only [Execution.MemReads,Execution.recordTensorRead,Execution.recordTensorEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rw [readSlot_readByte_other hcoords]
        rfl
      · simp only [Execution.MemReads,Execution.recordTensorRead,Execution.recordTensorEffects,
          ite_eq_right hj]
        rfl

theorem tensorReadFrame_writes (ho : X.tensor i=some o) (e : Ref) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp only [Execution.MemWrites,Execution.recordTensorRead,Execution.recordTensorEffects,
          ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
        rfl
      · simp only [Execution.MemWrites,Execution.recordTensorRead,Execution.recordTensorEffects,
          ite_eq_right hj]
        rfl

theorem tensorReadFrame_reads_self {address : Nat}
    (hsource : TensorCopy.source o.spec slot=.global address)
    {a : Acc} {bs : List (Option Byte)}
    (he : (Y).MemReads (tensorSlotReadRef i slot) a bs) :
    a.loc=⟨.global,0,address⟩ ∧ a.size=1 ∧ bs=[some value] := by
  obtain ⟨old,mapAddress,b,hobs,hissue,hloc,hread,hsize,hbs⟩ := he
  have ht : (Y).tensor i=some (o.readSlot slot value) := by
    simp [Execution.recordTensorRead,Execution.recordTensorEffects]
  have heq := Option.some.inj (ht.symm.trans hobs)
  subst old
  have hbyte : TensorCopy.readByte (o.readSlot slot value)
      slot.1.val slot.2.1.val slot.2.2.val=some value := by
    simp [TensorCopy.readByte,TensorCopy.Observation.readSlot,slotAt_self]
  have hb : b=value := Option.some.inj (hread.symm.trans hbyte)
  have hlocation : TensorCopy.readLoc (o.readSlot slot value).spec
      slot.1.val slot.2.1.val slot.2.2.val=some ⟨.global,0,address⟩ := by
    simp [Observation.readSlot,TensorCopy.readLoc_source,slotAt_self,hsource]
  exact ⟨Option.some.inj (hloc.symm.trans hlocation),hsize,by simpa only [hb] using hbs⟩

theorem tensorReadFrame_modelCausality (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f :=
  tensorByteFrame_modelCausality (X := X) (i := i) (o := o.readSlot slot value)
    (rf := fun e k => if e=tensorSlotReadRef i slot then none else X.rf e k)
    (by simp [ho,hn]) hn
    (by intro e k; simp [tensorSlotReadRef]) l e f

private theorem tensorReadFrame_byteCausality (ho : X.tensor i=some o)
    (hn : o.effects.notified=false)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (tensorReadFrame_modelCausality ho hn l e f).mp) (fun h => h)

theorem tensorReadFrame_le (ho : X.tensor i=some o) (hmissing : o.effects.read slot=none) :
    X.le Y := by
  apply Execution.le_recordTensorEffects
  · intro old hold
    have heq := Option.some.inj (ho.symm.trans hold)
    subst old
    exact readSlot_extends hmissing
  · intro e k hread
    by_cases he : e=tensorSlotReadRef i slot
    · subst e
      obtain ⟨a,bs,hread⟩ := hread
      exact (tensorReadFrame_no_old_read ho hmissing a bs hread).elim
    · simp [he]

theorem tensorReadFrame_size (ho : X.tensor i=some o) (hmissing : o.effects.read slot=none)
    (hg : i.1<L.threads) (hi : i.2<(X.tr i.1).length) : X.size L<(Y).size L := by
  apply recordTensorEffects_size_of_measure hg hi
  rw [ho]
  change o.effects.size<(o.readSlot slot value).effects.size
  rw [readSlot_size hmissing]
  omega
theorem tensorReadFrame_present_other (ho : X.tensor i=some o) {j : EvId} {p : Part}
    (hne : Ref.async j p≠tensorSlotReadRef i slot) : (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  case readLoad x y k =>
    by_cases hj : j=i
    · subst j
      have hcoords : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val) := by
        rintro ⟨rfl,rfl,rfl⟩
        exact hne rfl
      simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rw [readSlot_readByte_other hcoords]
    · simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ite_eq_right hj]
  case writeLoad x y k =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_and_left,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ite_eq_right hj]
  case notifyLoad =>
    by_cases hj : j=i
    · subst j
      simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ↓reduceIte,ho,Option.some.injEq,exists_eq_left']
      rfl
    · simp only [Execution.AsyncPresent,Execution.recordTensorRead,Execution.recordTensorEffects,
        ite_eq_right hj]

theorem tensorReadFrame_refPresent_other (ho : X.tensor i=some o) {e : Ref}
    (hne : e≠tensorSlotReadRef i slot) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p => exact tensorReadFrame_present_other ho hne

theorem tensorReadFrame_write_absent (ho : X.tensor i=some o)
    (hc : CopyOk o.spec o.effects) (hmissing : o.effects.read slot=none)
    {address : Nat} (hs : TensorCopy.source o.spec slot=.global address) :
    ¬(Y).AsyncPresent i (.write (.load slot.1.val slot.2.1.val slot.2.2.val)) := by
  have _ := ho
  have hw : o.effects.write slot=none := by
    cases hwrite : o.effects.write slot with
    | none => rfl
    | some content =>
      have hh := hc.writes slot content hwrite
      rw [hs] at hh
      obtain ⟨byte,hr,_⟩ := hh
      rw [hmissing] at hr
      cases hr
  intro hp
  obtain ⟨old,q,content,hobs,hslot,hwrite⟩ := hp
  have ht : (Y).tensor i=some (o.readSlot slot value) := by
    simp [Execution.recordTensorRead,Execution.recordTensorEffects]
  have heq := Option.some.inj (ht.symm.trans hobs)
  subst old
  have hq : slot=q := Option.some.inj ((slotAt_self slot).symm.trans hslot)
  subst q
  change o.effects.write slot=some content at hwrite
  rw [hw] at hwrite
  cases hwrite


end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {address : Nat}
local notation "Y" => X.recordTensorRead i o slot value

theorem tensorReadMemory_rf (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hsource : TensorCopy.source o.spec slot=.global address)
    (hmem : mem0 ⟨.global,0,address⟩=some (some value)) : RfWf mem0 Y := by
  intro e a bs he
  by_cases hid : e=tensorSlotReadRef i slot
  · subst e
    obtain ⟨hloc,hsize,hbs⟩ := tensorReadFrame_reads_self hsource he
    refine ⟨by simp [hbs,hsize],?_⟩
    intro k hk
    have hk0 : k=0 := by omega
    subst k
    have hrf0 : (Y).rf (tensorSlotReadRef i slot) 0=none := by
      simp [Execution.recordTensorRead,Execution.recordTensorEffects]
    rw [hrf0]
    change ∀c,mem0 (a.loc.at 0)=some c → bs[0]?=some ((Y).initialByte c (a.loc.at 0))
    intro c hc
    rw [Loc.at,Nat.add_zero,hloc,hmem] at hc
    have hcc := Option.some.inj hc
    subst c
    simp [hbs,Execution.initialByte]
  · have oldRead := (tensorReadFrame_reads_other ho hid a bs).mp he
    obtain ⟨hlen,hr⟩ := hX.rf e a bs oldRead
    refine ⟨hlen,?_⟩
    intro k hk
    have hs := hr k hk
    change match (if e=tensorSlotReadRef i slot then none else X.rf e k) with
      | none => _
      | some w => _
    rw [ite_eq_right hid]
    cases hsrc : X.rf e k with
    | none => simp only [hsrc] at hs ⊢; exact hs
    | some w =>
      rw [hsrc] at hs
      obtain ⟨dst,bytes,hw,hcover,hbyte⟩ := hs
      exact ⟨dst,bytes,(tensorReadFrame_writes ho w dst bytes).mpr hw,hcover,hbyte⟩

theorem tensorReadMemory_noFuture (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false) : NoFuture L Y := by
  intro e a bs k w he hk hr hvis
  by_cases hid : e=tensorSlotReadRef i slot
  · subst e
    simp only [Execution.recordTensorRead,Execution.recordTensorEffects,↓reduceIte,
      reduceCtorEq] at hr
  · have oldRead := (tensorReadFrame_reads_other ho hid a bs).mp he
    have oldRf : X.rf e k=some w := by
      simpa only [Execution.recordTensorRead,Execution.recordTensorEffects,
        ite_eq_right hid] using hr
    exact hX.noFuture e a bs k w oldRead hk oldRf
        (tensorReadFrame_byteCausality ho hn hvis)

theorem tensorReadMemory_hidden (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hsource : TensorCopy.source o.spec slot=.global address)
    (hnw : ∀w dst bytes,X.MemWrites w dst bytes → ¬dst.Covers ⟨.global,0,address⟩) :
    Hidden L Y := by
  intro e a bs k w dst bytes he hk hw hcover hvis
  have oldWrite := (tensorReadFrame_writes ho w dst bytes).mp hw
  by_cases hid : e=tensorSlotReadRef i slot
  · subst e
    obtain ⟨hloc,hsize,_⟩ := tensorReadFrame_reads_self hsource he
    have hk0 : k=0 := by omega
    have hc : dst.Covers ⟨.global,0,address⟩ := by
      simpa only [hk0,Loc.at,Nat.add_zero,hloc] using hcover
    exact (hnw w dst bytes oldWrite hc).elim
  · have oldRead := (tensorReadFrame_reads_other ho hid a bs).mp he
    have hh := hX.hidden e a bs k w dst bytes oldRead hk oldWrite hcover
      (tensorReadFrame_byteCausality ho hn hvis)
    change match (if e=tensorSlotReadRef i slot then none else X.rf e k) with
      | none => _
      | some source => _
    rw [ite_eq_right hid]
    cases hsrc : X.rf e k with
    | none => rw [hsrc] at hh; exact hh
    | some source =>
      rw [hsrc] at hh
      intro hbefore
      exact hh (tensorReadFrame_byteCausality ho hn hbefore)

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {address : Nat}
local notation "Y" => X.recordTensorRead i o slot value

theorem tensorReadFrame_read_absent (ho : X.tensor i=some o)
    (hmissing : o.effects.read slot=none) :
    ¬X.AsyncPresent i (.read (.load slot.1.val slot.2.1.val slot.2.2.val)) := by
  rintro ⟨old,hobs,hread⟩
  have heq : o=old := Option.some.inj (ho.symm.trans hobs)
  subst old
  rw [readByte_slot,hmissing] at hread
  cases hread

/-- The new read stage starts no stage edge: the write of its slot needs the read. -/
theorem tensorReadWaiting_no_edge (ho : X.tensor i=some o)
    (hc : CopyOk o.spec o.effects) (hmissing : o.effects.read slot=none)
    (hs : TensorCopy.source o.spec slot=.global address) (f : Ref) :
    ¬StageEdge Y (tensorSlotReadRef i slot) f := by
  intro ha
  unfold tensorSlotReadRef at ha
  cases f with
  | thread j => exact ha
  | async j p =>
    cases p <;> try exact ha
    all_goals obtain ⟨he,hslot,_,hw⟩ := ha
    all_goals cases hslot
    cases he
    exact tensorReadFrame_write_absent ho hc hmissing hs hw

/-- The new read stage and the returns of the waits it witnesses form a sink; outside them every
order relation is old. -/
theorem tensorReadWaiting_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o) (hc : CopyOk o.spec o.effects)
    (hmissing : o.effects.read slot=none)
    (hs : TensorCopy.source o.spec slot=.global address) :
    SinkFrame L K A X Y (CompletionNodes L Y (· = tensorSlotReadRef i slot)) :=
  sinkFrame_effect hX (· = tensorSlotReadRef i slot) (fun _ h => by cases h)
    (fun _ _ he => by cases he; exact tensorReadFrame_read_absent ho hmissing)
    (fun _ he h => (tensorReadFrame_refPresent_other ho he).mp h)
    (recordTensorEffects_needs hX.tma.2.2.1 (by simp [ho,Observation.readSlot]))
    (fun _ _ => by simp [tensorSlotReadRef])
    (fun _ _ _ _ h => recordTensorEffects_asyncObserved (o := o.readSlot slot value)
      (fun h => ⟨o,ho,rfl,h⟩) h)
    (fun _ f he => he ▸ tensorReadWaiting_no_edge ho hc hmissing hs f)
    (fun m r hr he => by
      have hm := ((hX.tma.2.2.1 m).2.1 r hr).1
      rw [he] at hm
      simp [objectAction,tensorSlotReadRef] at hm)

theorem tensorReadWaiting_order {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=some o)
    (hmissing : o.effects.read slot=none)
    (hs : TensorCopy.source o.spec slot=.global address) : OrderOk L K A Y :=
  (tensorReadWaiting_sinkFrame hX ho (hX.tensor i o ho).2.1 hmissing hs).orderOk hX.orderOk

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorCopy
noncomputable section

/-- Record an immutable initialized global source byte of a pending TMA. No
memory/visibility/waiting assumption about the candidate execution is supplied. -/
theorem tensor_read_counted_extension {L : Launch} {K : Kernel} {mem0 : Mem0}
    {A : List Assumption} (hA : ∀ a ∈ A, ∀ Z, a.wf L mem0 Z)
    {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {address : Nat}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hmissing : o.effects.read slot=none)
    (hs : TensorCopy.source o.spec slot=.global address)
    (hmem : mem0 ⟨.global,0,address⟩=some (some value))
    (hnw : ∀w dst bytes,X.MemWrites w dst bytes → ¬dst.Covers ⟨.global,0,address⟩) :
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
  let Y := X.recordTensorRead i o slot value
  have hconsistent : Consistent L K A mem0 Y := by
    apply consistent_recordTensorEffects (o := o.readSlot slot value) hX ⟨mapAddress,hi⟩
      (readSlot_copyOk hcopy hs hmissing) hrouting hvalid
      (by rw [ho]; rfl)
    · exact tensorReadMemory_rf hX ho hs hmem
    · exact tensorReadWaiting_order hX ho hmissing hs
    · exact tensorReadMemory_noFuture hX ho hn
    · exact tensorReadMemory_hidden hX ho hn hs hnw
    · intro e k
      simp [tensorSlotReadRef]
    · intro _ _ _ _
      simp [tensorSlotReadRef]
    · intro a ha
      exact hA a ha _
    · intro _ _ _
      simp [tensorSlotReadRef]
  exact ⟨Y,hconsistent,tensorReadFrame_le ho hmissing,tensorReadFrame_size ho hmissing hg hindex⟩

end
end PTX
end
