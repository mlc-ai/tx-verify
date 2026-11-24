-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorCompleteConsistentNotifyFrame

@[expose] public section

/-! A bytewise-complete pending tensor copy has a genuine counted Consistent
extension. Its actual object reply, including any checked error, is constructed
from perform. No RF/visibility/acyclicity/protocol premise remains. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- Record the notification of an actual bytewise-complete tensor load. This
applies to short executions and does not assume Safe or Complete. -/
theorem tensor_notify_counted_extension {L : Launch} {K : Kernel} {mem0 : Mem0}
    {A : List Assumption} (hA : ∀ a ∈ A, ∀ Z, a.wf L mem0 Z)
    {X : Execution} {i : EvId} {o : TensorCopy.Observation}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i=some o) (hn : o.effects.notified=false)
    (hw : ∀slot,∃value,o.effects.write slot=some value) :
    ∃Y,Consistent L K A mem0 Y ∧
      X.le Y ∧ X.size L<Y.size L := by
  obtain ⟨⟨address,hi⟩,hcopy,hrouting,hvalid⟩ := hX.tensor i o ho
  have hg : i.1<L.threads := by
    by_contra hh
    have hempty := hX.outside i.1 (by omega)
    obtain ⟨pc,he⟩ := hi
    simp only [Execution.get,hempty,List.getElem?_nil] at he
    cases he
  have hindex : i.2<(X.tr i.1).length := len_of_get hi.choose_spec
  let action := Action.completeTx (TensorTransfer.bytes o.spec.descriptor)
  let before := stateBefore (X.objects o.spec.mbar) (X.objects o.spec.mbar).length
  obtain ⟨rec,hid,ha,hok⟩ : ∃rec : Record Ref,
      rec.id=.async i (.notify .load) ∧ rec.action=action ∧ RecordOk before rec := by
    cases hp : perform before action with
    | ok reply =>
      refine ⟨⟨.async i (.notify .load),action,reply,none⟩,rfl,rfl,?_⟩
      simp [RecordOk,hp]
    | error err =>
      refine ⟨⟨.async i (.notify .load),action,⟨before,none,none⟩,some err⟩,rfl,rfl,?_⟩
      simp [RecordOk,hp]
  let Y := X.recordTensorNotification i o.notifiedObservation o.spec.mbar rec
  have hchecked := tensorNotification_checked_snoc hX.tma.2.2.1 (by simp [ho,hn]) hid hok
  have hconsistent : Consistent L K A mem0 Y := by
    apply consistent_recordTensorNotification (o := o.notifiedObservation) hX hi
      (TensorCopy.notifiedObservation_copyOk hcopy hw) hrouting hvalid rfl rfl
      (by simp [ho,hn]) hid ha hchecked
    · exact tensorNotifyFrame_rf hX ho
    · exact (tensorNotifyFrame_sinkFrame hX ho hn hid).orderOk hX.orderOk
    · exact tensorNotifyFrame_noFuture hX ho hn hid
    · exact tensorNotifyFrame_hidden hX ho hn hid
    · intro a ha
      exact hA a ha _
  refine ⟨Y,hconsistent,?_,notifiedObservation_counted ho hn hg hindex⟩
  apply Execution.le_recordTensorNotification
  intro prior hp
  have heq := Option.some.inj (ho.symm.trans hp)
  subst prior
  exact TensorCopy.notifiedObservation_extends o

end
end PTX
