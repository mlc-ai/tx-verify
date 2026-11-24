-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
public import Core.Tc.TcMmaConflicts
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TcMmaResultLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread

/-- Completion between an MMA and an ordinary store using the same tile. -/
def TensorMmaStoreOrder (l : Launch) (X : Execution) (tile : TensorStoreTile) : Prop :=
  ∀ mma store cell, StoreCell l X store cell → TensorStoreFootprint l store cell tile →
    MmaAccumulatorOn X mma cell tile → DoneBefore l X mma store ∨ StoreDoneBefore l X store mma

/-- The two tile protocols that share accumulator storage with ordinary stores. -/
structure TensorMixedWriteOrder (l : Launch) (X : Execution) : Prop where
  scoreProbability (stage : Fin 2) : TensorMmaStoreOrder l X (.probability stage)
  outputRescale (stage : Fin 2) : TensorMmaStoreOrder l X (.rescale stage)

/-- Completion for ordinary stores sharing a Tensor Memory A operand. -/
def TensorAStoreOrder (l : Launch) (X : Execution) : Prop :=
  ∀ reader store cell tile, X.MmaACell reader cell → StoreCell l X store cell →
    TensorStoreFootprint l store cell tile →
      StoreDoneBefore l X store reader ∨ DoneBefore l X reader store

/-- The earlier MMA store of a cell and a later Tensor Memory A read share a phase protocol. -/
def EarlierMmaAOrder (l : Launch) (X : Execution) : Prop :=
  ∀ reader writer cell, X.MmaACell reader cell → X.MmaCell writer cell →
    writer.2 < reader.2 → WriteBefore l X writer reader ∨ ReadBefore l X .a reader writer

private theorem storeOrMmaWrite {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {cell : Cell}
    (hi : TmemWrite l X i cell) : X.MmaCell i cell ∨ StoreCell l X i cell := by
  rcases hi with hMma | hStore | hCopy | hShift
  · exact .inl hMma
  · exact .inr hStore
  · obtain ⟨_,_,_,_,hCopy,_⟩ := hCopy
    exact (noTensorCopyOperandIssue hX hCopy).elim
  · obtain ⟨_,hShift,_⟩ := hShift
    exact (noTensorShiftIssue hX hShift).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem mixedStoreCompletion (hOrder : TensorMixedWriteOrder l X) {mma store : EvId}
    {d row col : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat} {cell : Cell}
    (hMma : X.MmaIssue mma d op accum mask) (hc : resultCell op d row col = some cell)
    (hStore : StoreCell l X store cell) :
    DoneBefore l X mma store ∨ StoreDoneBefore l X store mma := by
  obtain ⟨tile,hFootprint⟩ := tensorStoreFootprint hp hX hStore
  have hTile := mmaAccumulatorOnStoreTile hp hX hFootprint hMma hc
  cases tile with
  | probability stage =>
    exact hOrder.scoreProbability stage mma store cell hStore hFootprint hTile
  | rescale stage =>
    exact hOrder.outputRescale stage mma store cell hStore hFootprint hTile

private theorem mixedWritesOrdered (hOrder : TensorMixedWriteOrder l X) {mma store : EvId}
    {cell : Cell} (hMma : X.MmaCell mma cell) (hStore : StoreCell l X store cell) :
    WriteBefore l X mma store ∨ WriteBefore l X store mma := by
  obtain ⟨d,op,acc,mask,row,col,hIssue,hResult⟩ := hMma
  rcases mixedStoreCompletion hp hX hOrder hIssue (writeCell_resultCell hResult) hStore with h | h
  · exact .inl (.inl (.inl h))
  · exact .inr (.inr (.inl h))

/-- Write conflicts reduce to completion of the probability and rescale protocols. -/
theorem tensorWritesSafe (hOrder : TensorMixedWriteOrder l X) : WritesSafe l X := by
  intro i j cell hi hj
  rcases storeOrMmaWrite hX hi with hi | hi <;>
    rcases storeOrMmaWrite hX hj with hj | hj
  · exact mmaWritesOrdered hp hX hi hj
  · exact .inr (mixedWritesOrdered hp hX hOrder hi hj)
  · exact .inr ((mixedWritesOrdered hp hX hOrder hj hi).symm)
  · exact tensorStoreWritesOrdered hp hX hi hj

/-- Accumulator conflicts reduce to the same probability and rescale completion facts. -/
theorem tensorAccumulatorReadSafe (hOrder : TensorMixedWriteOrder l X) {reader writer : EvId}
    {cell : Cell} (hr : X.MmaReadCell reader cell) (hw : TmemWrite l X writer cell) :
    reader = writer ∨ WriteBefore l X writer reader ∨ ReadBefore l X .acc reader writer := by
  rcases storeOrMmaWrite hX hw with hMma | hStore
  · exact mmaAccumulatorReadOrdered hp hX hr hMma
  · obtain ⟨d,op,mask,row,col,hIssue,hResult⟩ := hr
    rcases mixedStoreCompletion hp hX hOrder hIssue hResult hStore with h | h
    · exact .inr (.inr (.inr (.inl h)))
    · exact .inr (.inl (.inr (.inl h)))

/-- Read conflicts use the mixed writes, ordering of stores with A and earlier QK completion. -/
theorem tensorReadsSafe (hMixed : TensorMixedWriteOrder l X) (hStore : TensorAStoreOrder l X)
    (hA : EarlierMmaAOrder l X) : ReadsSafe l X := by
  rw [readsSafe_iff]
  refine ⟨fun _ _ _ hr hw => tensorAccumulatorReadSafe hp hX hMixed hr hw,?_,?_⟩
  · intro reader writer cell hr hw
    rcases storeOrMmaWrite hX hw with hw | hw
    · have hLane := mmaAAndDLane hp hX hr hw
      rcases lt_trichotomy reader.2 writer.2 with hLt | hEq | hLt
      · exact .inr (.inr (earlierMmaAOperandOrdered hp hX hr hw hLt))
      · exact .inl (Prod.ext hLane hEq)
      · exact .inr (hA reader writer cell hr hw hLt)
    · obtain ⟨tile,hFootprint⟩ := tensorStoreFootprint hp hX hw
      rcases hStore reader writer cell tile hr hw hFootprint with h | h
      · exact .inr (.inl (.inr (.inl h)))
      · exact .inr (.inr (.inr (.inl h)))
  · rintro _ _ _ ⟨_,hShift,_⟩ _
    exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
