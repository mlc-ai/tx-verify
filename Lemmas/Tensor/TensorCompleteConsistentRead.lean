-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorCompleteConsistent
public import Lemmas.Async.AsyncChain
public import Lemmas.Order.Order
public import Lemmas.Tensor.TensorReadSources

@[expose] public section

section
/-! Unnotified tensor byte growth creates no new publication edge. Intent
footprints already exist at issue, and new byte effects cannot be an interior
junction without their own completion observation. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorCopy.Observation}
  {rf : Ref → Nat → Option Ref}
local notation "Y" => X.recordTensorEffects i o rf

theorem tensor_unnotified_not_observed {X : Execution} {i w : EvId} {acq : Bool} {ws : MbarScope}
    (hn : (X.tensor i).any (fun old => old.effects.notified)=false) :
    ¬AsyncObserved X i (.notify .load) w acq ws := by
  intro h
  obtain ⟨old,address,ho,_,hnotified,_⟩ := h.tensor
  have hh : (X.tensor i).any (fun old => old.effects.notified)=true := by
    simpa only [ho,Option.any_some] using hnotified
  rw [hn] at hh
  cases hh

/-- A tensor-effect update that sets no new notification adds no observed notification. -/
theorem recordTensorEffects_asyncObserved {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    {rf : Ref → Nat → Option Ref}
    (hn : o.effects.notified=true →
      ∃old,X.tensor i=some old ∧ old.spec=o.spec ∧ old.effects.notified=true)
    {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved (X.recordTensorEffects i o rf) j p w acq ws) :
    AsyncObserved X j p w acq ws := by
  obtain ⟨n, m, hN, hW⟩ := h
  refine ⟨n, m, ?_, hW⟩
  revert hN
  unfold Notifies
  split
  all_goals first
    | exact id
    | split
      · rename_i t _
        cases t with
        | load =>
          rintro ⟨hn', obs, a, ht, hi, hm, hnot⟩
          obtain ⟨old, hold, hsp, hno⟩ := recordTensorEffects_notified hn j obs ht hnot
          exact ⟨hn', old, a, hold, hsp ▸ hi, hsp ▸ hm, hno⟩
        | _ => exact id
      · exact id

theorem tensorByteFrame_tensorObserved
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hn : o.effects.notified=false) (j w : EvId) (acq : Bool) (ws : MbarScope) :
    AsyncObserved Y j (.notify .load) w acq ws ↔ AsyncObserved X j (.notify .load) w acq ws := by
  by_cases hj : j=i
  · subst j
    exact ⟨fun h => (tensor_unnotified_not_observed
      (by simp [Execution.recordTensorEffects,hn]) h).elim,
      fun h => (tensor_unnotified_not_observed hold h).elim⟩
  · have ht : (Y).tensor j=X.tensor j := by simp [Execution.recordTensorEffects,hj]
    simp only [AsyncObserved,Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,ht]
    rfl

/-- The stages that a group wait waits for are not tensor-load stages, so their presence is
unchanged. -/
theorem tensorByteFrame_groupPresent (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages Y j k, (Y).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl <;> exact Iff.rfl

theorem tensorByteFrame_finished
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hn : o.effects.notified=false) (j : EvId) (p : Part) (w : EvId) :
    AsyncFinished L Y j p w ↔ AsyncFinished L X j p w := by
  unfold AsyncFinished
  refine or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
    tensorByteFrame_groupPresent j k) ?_
  cases p <;> try exact Iff.rfl
  case readLoad x y k =>
    exact exists_congr fun ws =>
      and_congr_left' (tensorByteFrame_tensorObserved hold hn j w true ws)
  case writeLoad x y k =>
    exact exists_congr fun ws =>
      and_congr_left' (tensorByteFrame_tensorObserved hold hn j w true ws)
  case notifyLoad =>
    exact exists_congr fun ws =>
      and_congr_left' (tensorByteFrame_tensorObserved hold hn j w true ws)

theorem tensorByteFrame_onlyFinished (j : EvId) (p : Part) (w : EvId) :
    AsyncOnlyFinished Y j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => tensorByteFrame_groupPresent j _

theorem tensorByteFrame_covers (j : EvId) (p : Part) (l : Loc) :
    AsyncCovers Y j p l ↔ AsyncCovers X j p l := by cases p <;> rfl

theorem tensorByteFrame_present_other {j : EvId} {p : Part} (hj : j≠i) :
    (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> try rfl
  all_goals simp only [Execution.AsyncPresent,Execution.recordTensorEffects,ite_eq_right hj]

theorem tensorByteFrame_chain
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hn : o.effects.notified=false)
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (l : Loc) (a b : EvId × Part) : AsyncChain L Y l a b ↔ AsyncChain L X l a b := by
  have hd (a b : EvId × Part) : AsyncBefore L Y l a b ↔ AsyncBefore L X l a b :=
    AsyncBefore.congr (fun j p => tensorByteFrame_covers j p l)
      (tensorByteFrame_finished hold hn) tensorByteFrame_onlyFinished
      (fun _ _ _ _ => recordTensorEffects_baseCausality_iff hrf) (fun _ _ _ _ => Iff.rfl)
  apply AsyncChain.congr_on_edges hd
  rintro ⟨j,p⟩ b hedge
  by_cases hj : j=i
  · subst j
    cases p <;> try exact Iff.rfl
    all_goals
      first
      | obtain ⟨acc,w,hi,_⟩ := hedge.1
        exact (show False from hi.2).elim
      | rcases hedge.2.2 with ⟨w,hf,_⟩ | ⟨w,hf,_⟩
        · rcases hf with ⟨k,hv,-⟩ | ⟨ws,hf,-⟩
          · exact absurd hv (by rcases k with ⟨_ | _ | _⟩ | _ <;> simp [GroupWaitVisible])
          · exact (tensor_unnotified_not_observed (acq := true) (ws := ws)
              (by simp [Execution.recordTensorEffects,hn]) hf).elim
        · exact absurd hf.1 (by simp [GroupWaitVisible])
  · exact tensorByteFrame_present_other hj

theorem tensorByteFrame_modelCausality
    (hold : (X.tensor i).any (fun old => old.effects.notified)=false)
    (hn : o.effects.notified=false)
    (hrf : ∀e k,rf (.thread e) k=X.rf (.thread e) k)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f := by
  cases e with
  | thread e =>
    cases f with
    | thread f => exact or_congr (recordTensorEffects_baseCausality_iff hrf) Iff.rfl
    | async j p =>
      have hc := tensorByteFrame_covers (X := X) (i := i) (o := o) (rf := rf) j p l
      simp only [modelCausality,hc]
      unfold ProxyBefore
      simp only [recordTensorEffects_baseCausality_iff hrf]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hc := tensorByteFrame_covers (X := X) (i := i) (o := o) (rf := rf) j p l
      have hp : ∀ e f, ProxyBefore L Y e f l ↔ ProxyBefore L X e f l := by
        intro e f
        unfold ProxyBefore
        simp only [recordTensorEffects_baseCausality_iff hrf]
        rfl
      have hcb (w : EvId) :
          ObservedCompletionBefore L Y l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr rfl rfl (recordTensorEffects_baseCausality_iff hrf) (hp w f)
      simp only [modelCausality,hc,tensorByteFrame_finished hold hn,hcb]
    | async k q => exact and_congr_right fun _ => tensorByteFrame_chain hold hn hrf l (j,p) (k,q)

end
end PTX
end

section
/-! Recording a global source byte preserves the old tensor writes. Validity
comes from the real source classification, not from assuming copy completion. -/
namespace PTX.TensorCopy
noncomputable section

/-- Add one previously missing global source read, leaving writes/notify alone. -/
def Observation.readSlot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor)
    (value : Byte) : Observation :=
  ⟨o.spec,{o.effects with read := Function.update o.effects.read slot (some value)}⟩

theorem readSlot_copyOk {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} {address : Nat} (hc : CopyOk o.spec o.effects)
    (hsource : source o.spec slot=.global address) (hmissing : o.effects.read slot=none) :
    CopyOk (o.readSlot slot value).spec (o.readSlot slot value).effects := by
  constructor
  · intro (q : TensorTransfer.Slot o.spec.descriptor) byte hread
    by_cases hq : q=slot
    · subst q
      exact ⟨address,hsource⟩
    · apply hc.reads q byte
      simpa only [Observation.readSlot,Function.update_of_ne hq] using hread
  · intro (q : TensorTransfer.Slot o.spec.descriptor) content hwrite
    have hw : o.effects.write q=some content := hwrite
    have hvalid := hc.writes q content hw
    cases hs : source o.spec q with
    | fill mode format byte => simpa only [Observation.readSlot,hs] using hvalid
    | global addr =>
      simp only [Observation.readSlot,hs]
      rw [hs] at hvalid
      obtain ⟨old,hr,hcontent⟩ := hvalid
      by_cases hq : q=slot
      · subst q
        rw [hmissing] at hr
        cases hr
      · exact ⟨old,by simpa only [Observation.readSlot,Function.update_of_ne hq] using hr,hcontent⟩
  · intro hn q
    exact hc.complete hn q

theorem readSlot_extends {o : Observation} {slot : TensorTransfer.Slot o.spec.descriptor}
    {value : Byte} (hmissing : o.effects.read slot=none) :
    o.Extends (o.readSlot slot value) := by
  refine ⟨rfl,?_,fun _ _ h => h,fun h => h⟩
  intro (q : TensorTransfer.Slot o.spec.descriptor) byte hread
  by_cases hq : q=slot
  · subst q
    rw [hmissing] at hread
    cases hread
  · simpa only [Observation.readSlot,Function.update_of_ne hq] using hread

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
      (if o.effects.notified then 1 else 0)=
    o.effects.readSlots.card+o.effects.writeSlots.card+
      (if o.effects.notified then 1 else 0)+1
  omega

theorem slotAt_self {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    (slot : TensorTransfer.Slot d) :
    TensorTransfer.slotAt d slot.1.val slot.2.1.val slot.2.2.val=some slot := by
  rcases slot with ⟨⟨x,hx⟩,⟨y,hy⟩,⟨k,hk⟩⟩
  simp [TensorTransfer.slotAt,hx,hy,hk]

theorem slotAt_coordinates {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    {x y k : Nat} {slot : TensorTransfer.Slot d}
    (h : TensorTransfer.slotAt d x y k=some slot) :
    slot.1.val=x ∧ slot.2.1.val=y ∧ slot.2.2.val=k := by
  unfold TensorTransfer.slotAt at h
  split_ifs at h ; cases h
  exact ⟨rfl,rfl,rfl⟩

theorem readByte_slot (o : Observation) (slot : TensorTransfer.Slot o.spec.descriptor) :
    readByte o slot.1.val slot.2.1.val slot.2.2.val=o.effects.read slot := by
  simp [readByte,slotAt_self]

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
      have hh := slotAt_coordinates hq
      exact hne ⟨hh.1.symm,hh.2.1.symm,hh.2.2.symm⟩
    simp [Observation.readSlot,hq,Function.update_of_ne hqs]

end
end PTX.TensorCopy
end
