-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Wf
public import Lemmas.Step.TensorDrainInOrder
public import Lemmas.Kernel.Progress.Async

@[expose] public section

/-!
# A maximal execution has completed every tensor load, under a same-trace premise

Kernel-independent restatement of `Lemmas/Step/TensorDrainInOrder.lean` (a candidate to replace
it). The original takes `Assumption.WfStep`, which a kernel with an assumption about elections
cannot prove (`Wf.lean`), and uses it only for extensions that record one stage of a tensor
load: its empty observation, one source byte read, one byte written, its notification. Those
extensions have the same thread events and the same commit arrive-ons, so the premise here is
`WfSameTr` (`Wf.lean`). The statements and proofs are the original's, with that premise; the
text of the seven theorems was produced from the library file by substitution.

* `tensor_empty_consistent_sameTr`, `tensor_read_counted_extension_sameTr`,
  `tensor_write_counted_extension_sameTr`, `tensor_notify_counted_extension_sameTr`: the four
  stages.
* `tensor_first_step_sameTr`, `pending_tensor_sameTr`: an unnotified load whose global source
  bytes are defined at launch and never written (`TensorSources`) extends the execution by a
  counted stage.
* `tensor_all_notified_sameTr`: a maximal execution has completed every issued load.
* `tensor_stepsE`: the open tensor obligation of a maximal execution steps (the counterpart of
  `Sched.tensor_steps`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched AsyncCopy TensorCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Record a tensor load's empty observation. -/
theorem tensor_empty_consistent_sameTr (hA : WfSameTr L K mem0 A)
    (hX : Consistent L K A mem0 X) {i : EvId} {mapAddress : Nat} {spec : TensorCopy.Spec}
    (hi : X.TensorIssue i mapAddress spec) (hrouting : RoutingOk L (i.1 / L.block) spec)
    (hvalid : TensorDescriptor.Valid spec.descriptor) (ho : X.tensor i = none) :
    Consistent L K A mem0 (X.recordTensorEffects i (emptyObservation spec) X.rf) := by
  have hcopy : CopyOk (emptyObservation spec).spec (emptyObservation spec).effects := by
    constructor
    · intro q b hb; cases hb
    · intro q c hc; cases hc
    · intro hn; cases hn
  apply consistent_recordTensorEffects (o := emptyObservation spec) hX ⟨mapAddress, hi⟩
    hcopy hrouting hvalid (by rw [ho]; rfl)
  · exact tensorEmptyFrame_rf hX ho
  · exact (tensorEmptyFrame_sinkFrame hX ho).orderOk hX.orderOk
  · exact tensorEmptyFrame_noFuture hX ho
  · exact tensorEmptyFrame_hidden hX ho
  · intro e k
    rfl
  · intro _ _ _ _
    rfl
  · exact hA hX (tensorEmptyFrame_le ho) rfl rfl
  · intro _ _ _
    rfl

/-- Record an initialized global source byte of a pending tensor load. -/
theorem tensor_read_counted_extension_sameTr (hA : WfSameTr L K mem0 A)
    {i : EvId} {o : TensorCopy.Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Byte} {address : Nat}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i = some o) (hn : o.effects.notified = false)
    (hmissing : o.effects.read slot = none)
    (hs : TensorCopy.source o.spec slot = .global address)
    (hmem : mem0 ⟨.global, 0, address⟩ = some (some value))
    (hnw : ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, address⟩) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨⟨mapAddress, hi⟩, hcopy, hrouting, hvalid⟩ := hX.tensor i o ho
  have hg : i.1 < L.threads := by
    by_contra hh
    have hempty := hX.outside i.1 (by omega)
    obtain ⟨pc, he⟩ := hi
    simp only [Execution.get, hempty, List.getElem?_nil] at he
    cases he
  have hindex : i.2 < (X.tr i.1).length := len_of_get hi.choose_spec
  have hconsistent : Consistent L K A mem0 (X.recordTensorRead i o slot value) := by
    apply consistent_recordTensorEffects (o := o.readSlot slot value) hX ⟨mapAddress, hi⟩
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
    · exact hA hX (tensorReadFrame_le ho hmissing) rfl rfl
    · intro _ _ _
      simp [tensorSlotReadRef]
  exact ⟨_, hconsistent, tensorReadFrame_le ho hmissing,
    tensorReadFrame_size ho hmissing hg hindex⟩

/-- Record one valid pending tensor write without changing reads or RF. -/
theorem tensor_write_counted_extension_sameTr (hA : WfSameTr L K mem0 A)
    {i : EvId} {o : TensorCopy.Observation}
    {slot : TensorTransfer.Slot o.spec.descriptor} {value : Content}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i = some o) (hn : o.effects.notified = false)
    (hmissing : o.effects.write slot = none)
    (hv : TensorCopy.WriteValue o slot value) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨⟨mapAddress, hi⟩, hcopy, hrouting, hvalid⟩ := hX.tensor i o ho
  have hg : i.1 < L.threads := by
    by_contra hh
    have hempty := hX.outside i.1 (by omega)
    obtain ⟨pc, he⟩ := hi
    simp only [Execution.get, hempty, List.getElem?_nil] at he
    cases he
  have hindex : i.2 < (X.tr i.1).length := len_of_get hi.choose_spec
  have hconsistent : Consistent L K A mem0 (X.recordTensorWrite i o slot value) := by
    apply consistent_recordTensorEffects (o := o.writeSlot slot value) hX ⟨mapAddress, hi⟩
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
    · exact hA hX (tensorWriteFrame_le ho hmissing) rfl rfl
    · intro _ _ _
      rfl
  exact ⟨_, hconsistent, tensorWriteFrame_le ho hmissing,
    tensorWriteFrame_size ho hmissing hg hindex⟩

/-- Record the notification of a bytewise-complete tensor load. -/
theorem tensor_notify_counted_extension_sameTr (hA : WfSameTr L K mem0 A)
    {i : EvId} {o : TensorCopy.Observation}
    (hX : Consistent L K A mem0 X)
    (ho : X.tensor i = some o) (hn : o.effects.notified = false)
    (hw : ∀ slot, ∃ value, o.effects.write slot = some value) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨⟨address, hi⟩, hcopy, hrouting, hvalid⟩ := hX.tensor i o ho
  have hg : i.1 < L.threads := by
    by_contra hh
    have hempty := hX.outside i.1 (by omega)
    obtain ⟨pc, he⟩ := hi
    simp only [Execution.get, hempty, List.getElem?_nil] at he
    cases he
  have hindex : i.2 < (X.tr i.1).length := len_of_get hi.choose_spec
  let action := MBarrier.Action.completeTx (TensorTransfer.bytes o.spec.descriptor)
  let before := MBarrier.stateBefore (X.objects o.spec.mbar) (X.objects o.spec.mbar).length
  obtain ⟨rec, hid, ha, hok⟩ : ∃ rec : MBarrier.Record Ref,
      rec.id = .async i (.notify .load) ∧ rec.action = action ∧
        MBarrier.RecordOk before rec := by
    cases hp : MBarrier.perform before action with
    | ok reply =>
      refine ⟨⟨.async i (.notify .load), action, reply, none⟩, rfl, rfl, ?_⟩
      simp [MBarrier.RecordOk, hp]
    | error err =>
      refine ⟨⟨.async i (.notify .load), action, ⟨before, none, none⟩, some err⟩,
        rfl, rfl, ?_⟩
      simp [MBarrier.RecordOk, hp]
  have hle : X.le (X.recordTensorNotification i o.notifiedObservation o.spec.mbar rec) := by
    apply Execution.le_recordTensorNotification
    intro prior hp
    have heq := Option.some.inj (ho.symm.trans hp)
    subst prior
    exact TensorCopy.notifiedObservation_extends o
  have hchecked := tensorNotification_checked_snoc hX.tma.2.2.1 (by simp [ho, hn]) hid hok
  have hconsistent : Consistent L K A mem0
      (X.recordTensorNotification i o.notifiedObservation o.spec.mbar rec) := by
    apply consistent_recordTensorNotification (o := o.notifiedObservation) hX hi
      (TensorCopy.notifiedObservation_copyOk hcopy hw) hrouting hvalid rfl rfl
      (by simp [ho, hn]) hid ha hchecked
    · exact tensorNotifyFrame_rf hX ho
    · exact (tensorNotifyFrame_sinkFrame hX ho hn hid).orderOk hX.orderOk
    · exact tensorNotifyFrame_noFuture hX ho hn hid
    · exact tensorNotifyFrame_hidden hX ho hn hid
    · exact hA hX hle rfl rfl
  exact ⟨_, hconsistent, hle, notifiedObservation_counted ho hn hg hindex⟩

/-- A load's first step: record its empty observation and read or fill one byte. -/
theorem tensor_first_step_sameTr (hA : WfSameTr L K mem0 A)
    (hX : Consistent L K A mem0 X)
    (hts : TensorSources L mem0 X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (hi : X.TensorIssue i addr spec)
    (ho : X.tensor i = none) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  obtain ⟨hroute, hvalid, hbytes, hsrc⟩ := hts i addr spec hi
  let Z := X.recordTensorEffects i (emptyObservation spec) X.rf
  have hZ : Consistent L K A mem0 Z := tensor_empty_consistent_sameTr hA hX hi hroute hvalid ho
  have hzo : Z.tensor i = some (emptyObservation spec) := by
    simp [Z, Execution.recordTensorEffects]
  have hxz : X.le Z := tensorEmptyFrame_le ho
  have hsizeZ : Z.size L = X.size L := tensorEmptyFrame_size ho
  have hcard : 0 < Fintype.card (TensorTransfer.Slot spec.descriptor) := by
    rw [TensorTransfer.slot_card]
    exact hbytes
  obtain ⟨slot⟩ := Fintype.card_pos_iff.mp hcard
  cases hs : source spec slot with
  | global a =>
    obtain ⟨v, hmem, hnw⟩ := hsrc slot a hs
    have hnw' : ∀ w dst bytes, Z.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, a⟩ := by
      intro w dst bytes hw
      exact hnw w dst bytes (recordEmpty_memWrites hw)
    obtain ⟨Y, hY, hle, hsize⟩ :=
      tensor_read_counted_extension_sameTr hA hZ hzo rfl rfl hs hmem hnw'
    exact ⟨Y, hY, Execution.le_trans hxz hle, by simpa only [hsizeZ] using hsize⟩
  | fill mode format byte =>
    have hv : WriteValue (emptyObservation spec) slot (.filled mode format byte) := by
      simp only [WriteValue, emptyObservation, hs]
    obtain ⟨Y, hY, hle, hsize⟩ := tensor_write_counted_extension_sameTr hA hZ hzo rfl rfl hv
    exact ⟨Y, hY, Execution.le_trans hxz hle, by simpa only [hsizeZ] using hsize⟩

/-- **An unnotified load extends the execution.** -/
theorem pending_tensor_sameTr (hA : WfSameTr L K mem0 A)
    (hX : Consistent L K A mem0 X)
    (hts : TensorSources L mem0 X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (hi : X.TensorIssue i addr spec)
    (hn : (X.tensor i).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  cases ho : X.tensor i with
  | none => exact tensor_first_step_sameTr hA hX hts hi ho
  | some old =>
    have hnotified : old.effects.notified = false := by simpa only [ho, Option.any_some] using hn
    by_cases hw : ∀ slot, ∃ value, old.effects.write slot = some value
    · exact tensor_notify_counted_extension_sameTr hA hX ho hnotified hw
    · obtain ⟨slot, hslot⟩ : ∃ slot, old.effects.write slot = none := by
        by_contra hno
        apply hw
        intro slot
        cases hs : old.effects.write slot with
        | none => exact (hno ⟨slot, hs⟩).elim
        | some value => exact ⟨value, rfl⟩
      cases hs : source old.spec slot with
      | global a =>
        cases hr : old.effects.read slot with
        | none =>
          obtain ⟨⟨addr', hi'⟩, -⟩ := hX.tensor i old ho
          obtain ⟨v, hmem, hnw⟩ := (hts i addr' old.spec hi').2.2.2 slot a hs
          exact tensor_read_counted_extension_sameTr hA hX ho hnotified hr hs hmem hnw
        | some value =>
          have hv : WriteValue old slot (.copied value) := by simp [WriteValue, hs, hr]
          exact tensor_write_counted_extension_sameTr hA hX ho hnotified hslot hv
      | fill mode format byte =>
        have hv : WriteValue old slot (.filled mode format byte) := by simp [WriteValue, hs]
        exact tensor_write_counted_extension_sameTr hA hX ho hnotified hslot hv

/-- **A maximal execution has completed its tensor loads**, when their sources are fixed. -/
theorem tensor_all_notified_sameTr (hA : WfSameTr L K mem0 A)
    (hmax : Maximal L K A mem0 X)
    (hts : TensorSources L mem0 X) {i : EvId} {addr : Nat} {spec : TensorCopy.Spec}
    (hi : X.TensorIssue i addr spec) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  have hnotified : (X.tensor i).any (fun old => old.effects.notified) = true := by
    by_contra hn
    exact hmax.not_grows (pending_tensor_sameTr hA hmax.1 hts hi (Bool.eq_false_iff.mpr hn))
  cases ho : X.tensor i with
  | none => simp only [ho, Option.any_none, Bool.false_eq_true] at hnotified
  | some old => exact ⟨old, rfl, by simpa only [ho, Option.any_some] using hnotified⟩

/-- **A maximal execution whose tensor loads' sources are fixed has completed every load.** -/
theorem tensor_stepsE {M : Timed K A L} (hA : WfSameTr L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hts : TensorSources L mem0 X)
    (ho : Descent.Obl L X .tensor) : Steps M mem0 X .tensor :=
  (ho fun _ _ _ hi => tensor_all_notified_sameTr hA hmax hts hi).elim

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
