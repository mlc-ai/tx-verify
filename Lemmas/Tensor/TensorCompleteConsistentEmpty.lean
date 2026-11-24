-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tensor.TensorCompleteConsistentRead
public import Lemmas.Order.VisibilityFrame

@[expose] public section

namespace PTX
open AsyncCopy TensorCopy
noncomputable section

def TensorCopy.emptyObservation (spec : TensorCopy.Spec) : TensorCopy.Observation := ⟨spec,{}⟩

theorem TensorCopy.emptyObservation_readByte (spec : TensorCopy.Spec) (x y k : Nat) :
    readByte (emptyObservation spec) x y k=none := by
  change (TensorTransfer.slotAt spec.descriptor x y k).bind (fun _ => none)=none
  cases TensorTransfer.slotAt spec.descriptor x y k <;> rfl

theorem TensorCopy.emptyObservation_writeByte (spec : TensorCopy.Spec) (x y k : Nat) :
    writeByte (emptyObservation spec) x y k=none := by
  change (TensorTransfer.slotAt spec.descriptor x y k).bind (fun _ => none)=none
  cases TensorTransfer.slotAt spec.descriptor x y k <;> rfl

variable {L : Launch} {X : Execution} {i : EvId} {spec : TensorCopy.Spec}
local notation "Y" => X.recordTensorEffects i (TensorCopy.emptyObservation spec) X.rf

theorem tensorEmptyFrame_present (ho : X.tensor i=none) (j : EvId) (p : Part) :
    (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  by_cases hj : j=i
  · subst j
    cases p <;> try rfl
    all_goals simp [Execution.AsyncPresent,Execution.recordTensorEffects,ho,
      TensorCopy.emptyObservation,
      TensorCopy.readByte]
  · (cases p <;> simp only [Execution.AsyncPresent,Execution.recordTensorEffects,
      ite_eq_right hj]); rfl

theorem tensorEmptyFrame_reads (ho : X.tensor i=none) (e : Ref) (a : Acc)
    (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemReads,Execution.recordTensorEffects,ho,
          TensorCopy.emptyObservation_readByte]
      · simp only [Execution.MemReads,Execution.recordTensorEffects,ite_eq_right hj]
        rfl

theorem tensorEmptyFrame_writes (ho : X.tensor i=none) (e : Ref) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeLoad x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemWrites,Execution.recordTensorEffects,ho,
          TensorCopy.emptyObservation_writeByte]
      · simp only [Execution.MemWrites,Execution.recordTensorEffects,ite_eq_right hj]
        rfl

/-- Recording an empty observation adds no stage: every order relation is old. -/
theorem tensorEmptyFrame_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=none) :
    SinkFrame L K A X Y (CompletionNodes L Y (fun _ => False)) :=
  sinkFrame_effect hX (fun _ => False) (fun _ h => h) (fun _ _ h => h.elim)
    (fun e _ h => by
      cases e with
      | thread j => exact h
      | async j p => exact (tensorEmptyFrame_present ho j p).mp h)
    (recordTensorEffects_needs hX.tma.2.2.1 (by simp [ho, TensorCopy.emptyObservation]))
    (fun _ _ => rfl)
    (fun _ _ _ _ h => recordTensorEffects_asyncObserved (fun h => by cases h) h)
    (fun _ _ h => h.elim) (fun _ _ _ h => h)

theorem tensorEmptyFrame_modelCausality (ho : X.tensor i=none) (l : Loc) (e f : Ref) :
    modelCausality L Y l e f ↔ modelCausality L X l e f :=
  tensorByteFrame_modelCausality (by simp [ho]) rfl (fun _ _ => rfl) l e f
theorem tensorEmptyFrame_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=none) : RfWf mem0 Y := by
  intro e a bs he
  obtain ⟨hlen,hr⟩ := hX.rf e a bs ((tensorEmptyFrame_reads ho e a bs).mp he)
  refine ⟨hlen,?_⟩
  intro k hk
  have hs := hr k hk
  change match X.rf e k with
    | none => _
    | some w => _
  cases hsrc : X.rf e k with
  | none => simp only [hsrc] at hs ⊢; exact hs
  | some w =>
    rw [hsrc] at hs
    obtain ⟨dst,bytes,hw,hcover,hbyte⟩ := hs
    exact ⟨dst,bytes,(tensorEmptyFrame_writes ho w dst bytes).mpr hw,hcover,hbyte⟩

private theorem tensorEmptyFrame_byteCausality (ho : X.tensor i=none)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (tensorEmptyFrame_modelCausality ho l e f).mp) (fun h => h)

theorem tensorEmptyFrame_noFuture {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=none) : NoFuture L Y :=
  hX.noFuture.of_frame (fun e a bs => (tensorEmptyFrame_reads ho e a bs).mp) rfl
    (fun _ _ _ => tensorEmptyFrame_byteCausality ho)

theorem tensorEmptyFrame_hidden {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensor i=none) : Hidden L Y :=
  hX.hidden.of_frame (fun e a bs => (tensorEmptyFrame_reads ho e a bs).mp)
    (fun e a bs => (tensorEmptyFrame_writes ho e a bs).mp) rfl
    (fun _ _ _ => tensorEmptyFrame_byteCausality ho)

theorem tensorEmptyFrame_size (ho : X.tensor i=none) : (Y).size L=X.size L := by
  have hs (j : EvId) : (Y).asyncSize j=X.asyncSize j := by
    by_cases hj : j=i
    · subst j
      simp [Execution.asyncSize,Execution.recordTensorEffects,ho,
        TensorCopy.emptyObservation,Effects.size,Effects.readSlots,Effects.writeSlots]
      rfl
    · simp [Execution.asyncSize,Execution.recordTensorEffects,hj]
      rfl
  have ht : (Y).threadSize L=X.threadSize L := by
    unfold Execution.threadSize
    change ((List.range L.threads).map (fun g => (X.tr g).countP Event.counts+
      ((List.range (X.tr g).length).map (fun k => (Y).asyncSize (g,k))).sum)).sum=_
    simp only [hs]
  change (Y).threadSize L+X.pairSize L=X.size L
  rw [ht]
  rfl

theorem tensor_empty_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hA : ∀ a ∈ A, ∀ Z, a.wf L mem0 Z) {mapAddress : Nat}
    (hX : Consistent L K A mem0 X)
    (hi : X.TensorIssue i mapAddress spec) (hrouting : RoutingOk L (i.1/L.block) spec)
    (hvalid : TensorDescriptor.Valid spec.descriptor) (ho : X.tensor i=none) :
    Consistent L K A mem0 Y := by
  have hcopy : CopyOk (emptyObservation spec).spec (emptyObservation spec).effects := by
    constructor
    · intro q b hb; cases hb
    · intro q c hc; cases hc
    · intro hn; cases hn
  apply consistent_recordTensorEffects (o := emptyObservation spec) hX ⟨mapAddress,hi⟩
    hcopy hrouting hvalid (by rw [ho]; rfl)
  · exact tensorEmptyFrame_rf hX ho
  · exact (tensorEmptyFrame_sinkFrame hX ho).orderOk hX.orderOk
  · exact tensorEmptyFrame_noFuture hX ho
  · exact tensorEmptyFrame_hidden hX ho
  · intro e k
    rfl
  · intro _ _ _ _
    rfl
  · intro a ha
    exact hA a ha _
  · intro _ _ _
    rfl

theorem tensorEmptyFrame_le (ho : X.tensor i=none) : X.le Y := by
  apply Execution.le_recordTensorEffects
  · intro old hold
    rw [ho] at hold
    cases hold
  · intro e k _
    rfl


end
end PTX
