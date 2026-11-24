-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorStoreCompleteConsistent
public import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

/-! A missing shared source byte can be recorded without changing any old
store observation or closing the source interval. Dynamic RF/visibility is
separate from this instruction-local extension proof. -/
namespace PTX.TensorStore
noncomputable section

def Observation.readSlot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor)
    (value : Byte) : Observation :=
  ⟨o.spec,{o.effects with read:=Function.update o.effects.read slot (some value)}⟩

theorem readSlot_copyOk {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hc : CopyOk o.spec o.effects) (hn : o.effects.readsDone=false)
    (hmissing : o.effects.read slot=none) :
    CopyOk (o.readSlot slot value).spec (o.readSlot slot value).effects := by
  constructor
  · intro (q : TensorTransfer.Slot o.spec.descriptor) byte hwrite
    obtain ⟨hloc,source,hread,hvalue⟩ := hc.writes q byte hwrite
    refine ⟨hloc,source,?_,hvalue⟩
    by_cases hq : q=slot
    · subst q
      rw [hmissing] at hread
      cases hread
    · simpa only [Observation.readSlot,Function.update_of_ne hq] using hread
  · intro hdone
    change o.effects.readsDone=true at hdone
    rw [hn] at hdone
    cases hdone
  · intro hdone
    have hread := (hc.complete hdone).1
    rw [hn] at hread
    cases hread
  · exact hc.element
  · exact hc.old

theorem readSlot_extends {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hn : o.effects.readsDone=false) (hmissing : o.effects.read slot=none) :
    o.Extends (o.readSlot slot value) := by
  refine ⟨rfl,?_,fun _ _ h => h,fun h => h,fun h => h,?_,fun _ _ h => h⟩
  · intro (q : TensorTransfer.Slot o.spec.descriptor) byte hread
    by_cases hq : q=slot
    · subst q
      rw [hmissing] at hread
      cases hread
    · simpa only [Observation.readSlot,Function.update_of_ne hq] using hread
  · intro hdone
    rw [hn] at hdone
    cases hdone

theorem readSlot_size {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hmissing : o.effects.read slot=none) :
    (o.readSlot slot value).effects.size=o.effects.size+1 := by
  have hslots : (o.readSlot slot value).effects.readSlots=insert slot o.effects.readSlots := by
    change (Finset.univ.filter fun r : TensorTransfer.Slot o.spec.descriptor =>
      (Function.update o.effects.read slot (some value) r).isSome)=insert slot o.effects.readSlots
    ext q
    by_cases hq : q=slot
    · subst q
      simp [Effects.readSlots]
    · simp [Effects.readSlots,hq]
  have hnot : slot∉o.effects.readSlots := by simp [Effects.readSlots,hmissing]
  have hcard : (o.readSlot slot value).effects.readSlots.card=o.effects.readSlots.card+1 := by
    rw [hslots]
    exact Finset.card_insert_of_notMem hnot
  unfold Effects.size
  rw [hcard]
  change o.effects.readSlots.card+1+o.effects.writeSlots.card+
      (if o.effects.readsDone then 1 else 0)+(if o.effects.fullDone then 1 else 0)=
    o.effects.readSlots.card+o.effects.writeSlots.card+
      (if o.effects.readsDone then 1 else 0)+(if o.effects.fullDone then 1 else 0)+1
  omega

theorem readByte_slot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor) :
    readByte o slot.1.val slot.2.1.val slot.2.2.val=o.effects.read slot := by
  simp [readByte,TensorCopy.slotAt_self]

theorem readSlot_readByte_other {o : Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {x y k : Nat}
    (hne : ¬(x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val)) :
    readByte (o.readSlot slot value) x y k=readByte o x y k := by
  unfold readByte
  cases hq : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [Observation.readSlot,hq]
  | some q =>
    have hqs : q≠slot := by
      intro he
      subst q
      have hh := TensorCopy.slotAt_coordinates hq
      exact hne ⟨hh.1.symm,hh.2.1.symm,hh.2.2.symm⟩
    simp [Observation.readSlot,hq,Function.update_of_ne hqs]

/-- A performed reduction element keeps its bytes when a missing source byte is recorded: all
its source bytes were already read. -/
theorem readSlot_reduced {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hc : CopyOk o.spec o.effects) (hmissing : o.effects.read slot=none)
    (hr : o.spec.reduce.isSome) {x y : Nat}
    (hw : (writeByte (o.readSlot slot value) x y 0).isSome) (k : Nat) :
    writeByte (o.readSlot slot value) x y k=writeByte o x y k ∧
      oldByte (o.readSlot slot value) x y k=oldByte o x y k ∧
      readByte (o.readSlot slot value) x y k=readByte o x y k := by
  refine ⟨rfl,rfl,?_⟩
  by_cases hs : x=slot.1.val ∧ y=slot.2.1.val ∧ k=slot.2.2.val
  · exfalso
    obtain ⟨rfl,rfl,rfl⟩ := hs
    change ((TensorTransfer.slotAt o.spec.descriptor slot.1.val slot.2.1.val 0).bind
      o.effects.write).isSome at hw
    cases h0 : TensorTransfer.slotAt o.spec.descriptor slot.1.val slot.2.1.val 0 with
    | none => simp [h0] at hw
    | some s0 =>
      cases hb : o.effects.write s0 with
      | none => simp [h0,hb] at hw
      | some b =>
        have hc0 := TensorCopy.slotAt_coordinates h0
        obtain ⟨⟨b',hb'⟩,-⟩ := hc.element s0 b hb hr slot (Fin.ext hc0.1.symm)
          (Fin.ext hc0.2.1.symm)
        obtain ⟨-,src,hsrc,-⟩ := hc.writes slot b' hb'
        rw [hmissing] at hsrc
        cases hsrc
  · exact readSlot_readByte_other hs

/-- Required slots cannot be added after read completion; this is derived
from the actual store rules, not a progress precondition. -/
theorem missing_required_before_readDone {o : Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {loc : Loc}
    (hc : CopyOk o.spec o.effects) (hloc : destination o.spec slot=some loc)
    (hn : o.effects.read slot=none) : o.effects.readsDone=false := by
  cases hdone : o.effects.readsDone
  · rfl
  · obtain ⟨byte,hread⟩ := hc.readsComplete hdone slot loc hloc
    rw [hn] at hread
    cases hread

end
end PTX.TensorStore
