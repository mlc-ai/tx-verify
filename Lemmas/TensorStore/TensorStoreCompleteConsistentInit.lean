-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistentByteVisibility
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Execution.EffectFrame
public import Lemmas.Snoc.Snoc

@[expose] public section

/-! Initializing a store observation records no byte or completion stage.
This uncounted step must be composed with the next byte/flag extension. -/
namespace PTX
open AsyncCopy
noncomputable section

def TensorStore.emptyObservation (spec : TensorStore.Spec) : TensorStore.Observation := ⟨spec,{}⟩
def Execution.initStoreObservation (X : Execution) (i : EvId)
    (spec : TensorStore.Spec) : Execution :=
  X.recordStoreEffects i (TensorStore.emptyObservation spec) X.rf

theorem TensorStore.emptyObservation_readByte (spec : TensorStore.Spec) (x y k : Nat) :
    readByte (emptyObservation spec) x y k=none := by
  change (TensorTransfer.slotAt spec.descriptor x y k).bind (fun _ => none)=none
  cases TensorTransfer.slotAt spec.descriptor x y k <;> rfl

theorem TensorStore.emptyObservation_writeByte (spec : TensorStore.Spec) (x y k : Nat) :
    writeByte (emptyObservation spec) x y k=none := by
  change (TensorTransfer.slotAt spec.descriptor x y k).bind (fun _ => none)=none
  cases TensorTransfer.slotAt spec.descriptor x y k <;> rfl

theorem TensorStore.emptyObservation_oldByte (spec : TensorStore.Spec) (x y k : Nat) :
    oldByte (emptyObservation spec) x y k=none := by
  change (TensorTransfer.slotAt spec.descriptor x y k).bind (fun _ => none)=none
  cases TensorTransfer.slotAt spec.descriptor x y k <;> rfl

variable {L : Launch} {X : Execution} {i : EvId} {spec : TensorStore.Spec}
local notation "Y" => X.initStoreObservation i spec

theorem storeInit_reads (hn : X.tensorStores i=none) (e : Ref) (a : Acc) (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemReads,Execution.initStoreObservation,Execution.recordStoreEffects,
          TensorStore.emptyObservation_readByte,hn]
      · simp only [Execution.MemReads,Execution.initStoreObservation,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl
    case oldStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemReads,Execution.initStoreObservation,Execution.recordStoreEffects,
          TensorStore.emptyObservation_oldByte,hn]
      · simp only [Execution.MemReads,Execution.initStoreObservation,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem storeInit_writes (hn : X.tensorStores i=none) (e : Ref) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeStore x y k =>
      by_cases hj : j=i
      · subst j
        simp [Execution.MemWrites,Execution.initStoreObservation,Execution.recordStoreEffects,
          TensorStore.emptyObservation_writeByte,hn]
      · simp only [Execution.MemWrites,Execution.initStoreObservation,Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem storeInit_present (hn : X.tensorStores i=none) (j : EvId) (p : Part) :
    (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  by_cases hj : j=i
  · subst j
    cases p <;> try rfl
    all_goals simp [Execution.AsyncPresent,Execution.initStoreObservation,
      Execution.recordStoreEffects,
      TensorStore.emptyObservation_readByte,TensorStore.emptyObservation_writeByte,
      TensorStore.emptyObservation_oldByte,hn]
    all_goals simp [TensorStore.emptyObservation]
  · cases p <;> try rfl
    all_goals simp only [Execution.AsyncPresent,Execution.initStoreObservation,
      Execution.recordStoreEffects,ite_eq_right hj]

theorem storeInit_modelCausality (hn : X.tensorStores i=none) (l : Loc) (e f : Ref) :
    modelCausality L Y l e f ↔ modelCausality L X l e f :=
  storeByteFrame_modelCausality (by simp [hn]) (by simp [hn]) rfl rfl (fun _ _ => rfl) l e f

/-- Initializing the observation preserves the byte order of existing accesses. -/
theorem storeInit_byteCausality (hn : X.tensorStores i=none) (l : Loc) (e f : Ref) :
    ByteCausality L Y l e f ↔ ByteCausality L X l e f :=
  ⟨ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
      (fun {l e f} => (storeInit_modelCausality hn l e f).mp) (fun h => h),
    ByteCausality.of_same_context (L := L) (X := Y) («Y» := X) rfl rfl
      (fun {l e f} => (storeInit_modelCausality hn l e f).mpr) (fun h => h)⟩

/-- Initializing a store observation adds no stage: every order relation is old. -/
theorem storeInit_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.tensorStores i=none) :
    SinkFrame L K A X Y (CompletionNodes L Y (fun _ => False)) :=
  sinkFrame_effect hX (fun _ => False) (fun _ h => h) (fun _ _ h => h.elim)
    (fun e _ h => by
      cases e with
      | thread j => exact h
      | async j p => exact (storeInit_present hn j p).mp h)
    (recordStoreEffects_needs hX.tma.2.2.1) (fun _ _ => rfl) (fun _ _ _ _ h => h)
    (fun _ _ h => h.elim) (fun _ _ _ h => h)

theorem storeInit_rf {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hn : X.tensorStores i=none) : RfWf mem0 Y := by
  intro e a bs he
  obtain ⟨hlen,hvalues⟩ := hX.rf e a bs ((storeInit_reads hn _ _ _).mp he)
  refine ⟨hlen,?_⟩
  intro k hk
  have hv := hvalues k hk
  change match X.rf e k with
    | none => _
    | some w => _
  cases hsrc : X.rf e k with
  | none =>
    simp only [hsrc] at hv ⊢
    exact hv
  | some w =>
    rw [hsrc] at hv
    obtain ⟨dst,bytes,hw,hcov,hval⟩ := hv
    exact ⟨dst,bytes,(storeInit_writes hn _ _ _).mpr hw,hcov,hval⟩

theorem storeInit_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hi : ∃address,X.TensorStoreIssue i address spec)
    (hv : TensorStore.Valid (i.1/L.block) spec) (hn : X.tensorStores i=none)
    (hasm : ∀a∈A,a.wf L mem0 Y) : Consistent L K A mem0 Y := by
  have hc : TensorStore.CopyOk spec (TensorStore.emptyObservation spec).effects := by
    constructor
    · intro slot byte hwrite
      cases hwrite
    · intro hdone
      cases hdone
    · intro hdone
      cases hdone
    · intro slot byte hwrite
      cases hwrite
    · intro slot byte hold
      cases hold
  have hobs : ∀old,X.tensorStores i=some old → old.Extends (TensorStore.emptyObservation spec) := by
    intro old hold
    rw [hn] at hold
    cases hold
  apply consistent_recordStoreEffects (o:=TensorStore.emptyObservation spec) (rf:=X.rf)
    hX hi hv hc hobs
  · exact storeInit_rf hX hn
  · exact (storeInit_sinkFrame hX hn).orderOk hX.orderOk
  · exact NoFuture.of_frame hX.noFuture (fun _ _ _ h => (storeInit_reads hn _ _ _).mp h) rfl
      (fun l e f => (storeInit_byteCausality hn l e f).mp)
  · exact Hidden.of_frame hX.hidden (fun _ _ _ h => (storeInit_reads hn _ _ _).mp h)
      (fun _ _ _ h => (storeInit_writes hn _ _ _).mp h) rfl
      (fun l e f => (storeInit_byteCausality hn l e f).mp)
  · exact fun _ _ => rfl
  · refine recordStoreEffects_reduce hX.reduce (fun _ x y hw => ?_) (fun _ _ _ _ => rfl)
    simp [TensorStore.writeByte, TensorStore.emptyObservation] at hw
  · exact hasm
  · refine atomicOk_congr (X := X) («Y» := Y) (fun p l n => ?_)
      (fun _ _ => rmwStrong_congr rfl rfl)
      (fun p k => by cases p <;> rfl) hX.atomic
    cases p with
    | tensor j x y =>
      by_cases hj : j = i
      · subst j
        simp [Execution.RmwAt, TensorStore.Reduced, Execution.initStoreObservation,
          Execution.recordStoreEffects, hn, TensorStore.writeByte, TensorStore.emptyObservation]
      · simp [Execution.RmwAt, TensorStore.Reduced, Execution.initStoreObservation,
          Execution.recordStoreEffects, hj]
    | _ => exact Iff.rfl

theorem storeInit_le (hn : X.tensorStores i=none) : X.le Y := by
  apply Execution.le_recordStoreEffects
  · intro old hold
    rw [hn] at hold
    cases hold
  · exact fun _ _ _ => rfl

theorem storeInit_observation : (Y).tensorStores i=some (TensorStore.emptyObservation spec) := by
  simp [Execution.initStoreObservation,Execution.recordStoreEffects]

theorem storeInit_size (hn : X.tensorStores i=none) : (Y).size L=X.size L := by
  have hs (j : EvId) : (Y).asyncSize j=X.asyncSize j := by
    unfold Execution.asyncSize
    rw [show (Y).async=X.async from rfl,show (Y).clc=X.clc from rfl,
      show (Y).tensor=X.tensor from rfl,show (Y).tcNotified=X.tcNotified from rfl,
      show (Y).elemSize=X.elemSize from rfl,
      show (Y).tensorStores j=if j=i then some (TensorStore.emptyObservation spec)
        else X.tensorStores j from rfl]
    by_cases hj : j=i
    · subst j
      simp [TensorStore.emptyObservation,TensorStore.Effects.size_empty,hn]
    · simp only [hj,↓reduceIte]
  unfold Execution.size Execution.threadSize
  simp only [hs]
  rfl

end
end PTX
