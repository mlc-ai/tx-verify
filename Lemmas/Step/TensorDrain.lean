-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Drain
public import Lemmas.Tensor.TensorCompleteConsistentReadProgress
public import Lemmas.Tensor.TensorCompleteConsistentEmpty
public import Lemmas.Tensor.TensorCompleteConsistentWriteProgress
public import Lemmas.Tensor.TensorCompleteConsistentNotifyProgress
public import Lemmas.Tensor.TensorTransfer

@[expose] public section

/-! # A maximal execution has completed every tensor load whose sources are fixed

A proof tool. A tensor load that has not notified its barrier grows the execution by one counted
step: record its empty observation, read a global byte its box covers, write a byte of the box
(the byte read, or the descriptor's fill), or notify once every byte is written. Reading a global
byte needs its initial value and that no write covers it (`TensorSources`). So a maximal execution
has completed every tensor load (`Maximal.tensor_all_notified`). -/

namespace PTX

open TensorCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Each tensor load is routed and has a valid descriptor of a nonempty box, and each global byte
its box reads has an initial value that no write covers. -/
def TensorSources (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  ∀ i addr s, X.TensorIssue i addr s → RoutingOk L (i.1 / L.block) s ∧
    TensorDescriptor.Valid s.descriptor ∧ 0 < TensorTransfer.bytes s.descriptor ∧
    ∀ slot a, source s slot = .global a → ∃ v, mem0 ⟨.global, 0, a⟩ = some (some v) ∧
      ∀ w dst bytes, X.MemWrites w dst bytes → ¬ dst.Covers ⟨.global, 0, a⟩

/-- An empty observation of a load adds no write. -/
theorem recordEmpty_memWrites {i : EvId} {spec : TensorCopy.Spec} {w : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte}
    (h : (X.recordTensorEffects i (emptyObservation spec) X.rf).MemWrites w a bs) :
    X.MemWrites w a bs := by
  rcases w with e | ⟨j, p⟩
  · exact h
  · cases p with
    | writeLoad x y k =>
      obtain ⟨o, addr, b, ho, hti, hl, hb, rest⟩ := h
      simp only [Execution.recordTensorEffects] at ho
      split_ifs at ho with hj
      · cases ho
        simp [TensorCopy.writeByte, emptyObservation] at hb
      · exact ⟨o, addr, b, ho, hti, hl, hb, rest⟩
    | _ => exact h

/-- A load's first step: record its empty observation and read or fill one byte. -/
theorem tensor_first_step (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hts : TensorSources L mem0 X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (hi : X.TensorIssue i addr spec)
    (ho : X.tensor i = none) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  obtain ⟨hroute, hvalid, hbytes, hsrc⟩ := hts i addr spec hi
  let Z := X.recordTensorEffects i (emptyObservation spec) X.rf
  have hZ : Consistent L K A mem0 Z := tensor_empty_consistent hA hX hi hroute hvalid ho
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
    obtain ⟨Y, hY, hle, hsize⟩ := tensor_read_counted_extension hA hZ hzo rfl rfl hs hmem hnw'
    exact ⟨Y, hY, Execution.le_trans hxz hle, by simpa only [hsizeZ] using hsize⟩
  | fill mode format byte =>
    have hv : WriteValue (emptyObservation spec) slot (.filled mode format byte) := by
      simp only [WriteValue, emptyObservation, hs]
    obtain ⟨Y, hY, hle, hsize⟩ := tensor_write_counted_extension hA hZ hzo rfl rfl hv
    exact ⟨Y, hY, Execution.le_trans hxz hle, by simpa only [hsizeZ] using hsize⟩

/-- **An unnotified load extends the execution.** -/
theorem pending_tensor (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hts : TensorSources L mem0 X)
    {i : EvId} {addr : Nat} {spec : TensorCopy.Spec} (hi : X.TensorIssue i addr spec)
    (hn : (X.tensor i).any (fun old => old.effects.notified) = false) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  classical
  cases ho : X.tensor i with
  | none => exact tensor_first_step hA hX hts hi ho
  | some old =>
    have hnotified : old.effects.notified = false := by simpa only [ho, Option.any_some] using hn
    by_cases hw : ∀ slot, ∃ value, old.effects.write slot = some value
    · exact tensor_notify_counted_extension hA hX ho hnotified hw
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
          exact tensor_read_counted_extension hA hX ho hnotified hr hs hmem hnw
        | some value =>
          have hv : WriteValue old slot (.copied value) := by simp [WriteValue, hs, hr]
          exact tensor_write_counted_extension hA hX ho hnotified hslot hv
      | fill mode format byte =>
        have hv : WriteValue old slot (.filled mode format byte) := by simp [WriteValue, hs]
        exact tensor_write_counted_extension hA hX ho hnotified hslot hv

/-- **A maximal execution has completed its tensor loads**, when their sources are fixed. -/
theorem Maximal.tensor_all_notified (hA : Assumption.WfFree L mem0 A) (hmax : Maximal L K A mem0 X)
    (hts : TensorSources L mem0 X) {i : EvId} {addr : Nat} {spec : TensorCopy.Spec}
    (hi : X.TensorIssue i addr spec) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  have hnotified : (X.tensor i).any (fun old => old.effects.notified) = true := by
    by_contra hn
    exact hmax.not_grows (pending_tensor hA hmax.1 hts hi (Bool.eq_false_iff.mpr hn))
  cases ho : X.tensor i with
  | none => simp only [ho, Option.any_none, Bool.false_eq_true] at hnotified
  | some old => exact ⟨old, rfl, by simpa only [ho, Option.any_some] using hnotified⟩

end

end PTX
