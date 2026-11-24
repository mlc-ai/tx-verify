-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorStoreCompleteConsistentWriteFrame
public import Lemmas.Execution.EffectFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistent

@[expose] public section

section
namespace PTX
open AsyncCopy TensorStore MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation}
  {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte}
local notation "Y" => X.recordStoreWrite i o slot value
/-- The new store write starts no stage edge: the full completion of the store is absent. -/
theorem storeWriteWaiting_no_edge (hn : o.effects.fullDone=false) (f : Ref) :
    ¬StageEdge Y (storeSlotWriteRef i slot) f := by
  intro ha
  unfold storeSlotWriteRef at ha
  cases f with
  | thread j => exact ha
  | async j p =>
    cases p <;> try exact ha
    case fullDone =>
      obtain ⟨he,_,hw⟩ := ha
      cases he
      exact storeWriteFrame_no_fullDone hn hw
    all_goals
      obtain ⟨-, hm, -⟩ := ha
      simp [AsyncCopy.Part.target] at hm

/-- The new store write stage, when absent before, and the returns of the waits it witnesses form
a sink; outside them every order relation is old. -/
theorem storeWriteWaiting_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o) (hn : o.effects.fullDone=false) :
    SinkFrame L K A X Y
      (CompletionNodes L Y (fun x => x = storeSlotWriteRef i slot ∧ ¬ X.RefPresent x)) :=
  sinkFrame_effect hX (fun x => x = storeSlotWriteRef i slot ∧ ¬ X.RefPresent x)
    (fun _ h => by cases h.1) (fun _ _ he => he.2)
    (fun e he h => by
      by_cases hw : e = storeSlotWriteRef i slot
      · by_contra hx
        exact he ⟨hw, hx⟩
      · exact (storeWriteFrame_refPresent_other ho hw).mp h)
    (recordStoreEffects_needs hX.tma.2.2.1) (fun _ _ => rfl) (fun _ _ _ _ h => h)
    (fun _ f he => he.1 ▸ storeWriteWaiting_no_edge hn f)
    (fun m r hr he => by
      have hm := ((hX.tma.2.2.1 m).2.1 r hr).1
      rw [he.1] at hm
      simp [objectAction,storeSlotWriteRef] at hm)

theorem storeWriteWaiting_order {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o)
    (hn : o.effects.fullDone=false) : OrderOk L K A Y :=
  (storeWriteWaiting_sinkFrame hX ho hn).orderOk hX.orderOk

end
end PTX
end

section
namespace PTX
open AsyncCopy TensorStore
noncomputable section

 theorem consistent_storeWrite {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} {i : EvId} {o : TensorStore.Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {loc : Loc}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i=some o) (hred : o.spec.reduce=none)
    (hd : TensorStore.destination o.spec slot=some loc)
    (hr : o.effects.read slot=some value) (hn : o.effects.write slot=none)
    (hasm : ∀a∈A,a.wf L mem0 (X.recordStoreWrite i o slot value)) :
    Consistent L K A mem0 (X.recordStoreWrite i o slot value) := by
  obtain ⟨hi,hvalid,hcopy⟩ := hX.store i o ho
  have hf := missing_required_before_fullDone hcopy hd hn
  apply consistent_recordStoreEffects (o:=o.writeSlot slot value) (rf:=X.rf)
    hX hi hvalid (writeSlot_copyOk hcopy hred hd hr)
  · intro old hold
    have heq : old=o := Option.some.inj (hold.symm.trans ho)
    subst old
    exact writeSlot_extends hn
  · exact storeWriteFrame_rf hX.rf ho hn
  · exact storeWriteWaiting_order hX ho hf
  · exact hX.noFuture.of_frame (fun e a bs he => (storeWriteFrame_reads ho e a bs).mp he)
      rfl (fun _ _ _ => storeWriteFrame_byteCausality ho hf)
  · exact storeWriteFrame_hidden hX.hidden ho hf
  · intros; rfl
  · refine recordStoreEffects_reduce hX.reduce (fun hr' => ?_) (fun _ _ _ _ => rfl)
    change o.spec.reduce.isSome=true at hr'
    rw [hred] at hr'
    cases hr'
  · exact hasm
  · refine recordStoreEffects_atomicOk hX.atomic (fun old hold => ?_)
      (.update (fun _ => rfl) (fun hr' => ?_)) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ _ _ => rfl)
    · have heq : old=o := Option.some.inj (hold.symm.trans ho)
      subst old
      exact writeSlot_extends hn
    · change o.spec.reduce.isSome=true at hr'
      rw [hred] at hr'
      cases hr'

end
end PTX
end
