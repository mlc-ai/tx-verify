-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningPackedProbabilities
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityStoreOrder
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityCursor
import Kernels.TmlFa4Fwd.Proof.Thread.ActiveProbabilityStore
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxAffine
import Kernels.TmlFa4Fwd.Proof.Termination
import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof Thread.Scores

/-- The actual first store at a selected quarter is the store of the opening replay.
The argument only needs the corresponding part of that lane's trace to be present. -/
theorem OpeningAffineLane.observedStoreOfPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningAffineLane p l X g batch stage wait)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (q : Fin 4) (hRecorded : lane.entry.pos+1+probabilityTraceIndex q < (X.tr g).length)
    {store address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) = some ⟨probabilityPc .first q,.tc (.st address vals shape)⟩) :
    vals = (List.range 16).map
      (probabilityWord (fun col => lane.probabilityWeights (32*q.val+col))) := by
  let pos := lane.entry.pos+1+probabilityTraceIndex q
  let weights := fun col => lane.probabilityWeights (32*q.val+col)
  have hStore : X.get (g,pos) = some (firstStoreEvent l g stage q weights) := by
    by_cases hLast : q = 3
    · subst q
      have hBound : lane.entry.pos+7 < (X.tr g).length := by
        change lane.entry.pos+1+6 < (X.tr g).length at hRecorded
        omega
      exact lane.firstStoresOfPrefix hp hb hLo hHi hBound 3
    · have hEarly : q.val < 3 := by
        have hVal := q.isLt
        by_contra! h
        apply hLast
        exact Fin.ext (by omega)
      let quarter : Fin 3 := ⟨q.val,hEarly⟩
      have hIndex : probabilityTraceIndex q = q.val+1 := by
        fin_cases q <;> first | rfl | contradiction
      rw [hIndex] at hRecorded
      have hEarlyStore := lane.firstEarlyStoreOfPrefix hp hb hLo hHi quarter hRecorded
      dsimp only [pos]
      rwa [hIndex]
  have hEq := openingProbabilityStoreUnique hX q he hStore
  rw [hEq] at he
  have hKind := congrArg Event.kind (Option.some.inj (he.symm.trans hStore))
  obtain ⟨_,hValues,_⟩ := TcKind.st.inj (Kind.tc.inj hKind)
  exact hValues

/-- A recorded tensor store belongs to the lane's first probability publication. -/
def OpeningProbabilityStore (X : Execution) (store : EvId) : Prop :=
  ∃ (q : Fin 4) (address : Nat) (vals : List Value) (shape : TcShape),
    X.get store = some ⟨probabilityPc .first q,.tc (.st address vals shape)⟩

/-- Every observed opening probability store in a consistent prefix contains
the packed BF16 weights produced by its lane's actual first round. -/
theorem openingProbabilityStoreValues {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (q : Fin 4) {g store address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get (g,store) = some ⟨probabilityPc .first q,.tc (.st address vals shape)⟩) :
    ∃ (batch : Nat) (stage : Fin 2) (weights : Nat → ℝ),
      batch < p.batch ∧ tilePrefix p batch*p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧ Prologue.warpIndex l g/4 = stage.val ∧
      vals = (List.range 16).map (probabilityWord (fun col => weights (32*q.val+col))) ∧
      let coords := Epilogue.assignedCoordinates p batch (g/l.block)
      let row := 128*(2*coords.1+stage.val)+(g%l.block)%128
      let blocks := Mma.trips p batch coords.1
      row < p.qLength batch → ∀ col : Fin 128,
        weights col.val = shiftedWeight p batch coords.2 row (visitKey blocks 0 col.val)
          (firstReference p batch coords.2 row blocks) := by
  obtain ⟨Y,hY,hPrefix,hLargest⟩ := bounded_largest_extension (terminates hp) hX
  have hMax : Maximal l kernel Assumptions.all m Y :=
    ⟨hY,fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
  have hFrame := hFootprint Y hY
  have hEvent := Execution.le_get hPrefix he
  obtain ⟨hWork,stage,hStage⟩ :=
    probabilityStoreScheduled hp hY (hFrame.metadataProtected hp).1 .first q hEvent
  obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hWork
  obtain ⟨wait,⟨lane⟩⟩ := Progress.openingSoftmaxAffineOfAllStages hp hMax hFrame
    (event_thread_lt hY hEvent) stage hStage hb hLo hHi
  have hBound := lane.entry.probabilityStoreBound hp hY q hEvent
  refine ⟨batch,stage,lane.probabilityWeights,hb,hLo,hHi,hStage,?_,?_⟩
  · exact lane.observedStoreOfPrefix hp hY hb hLo hHi q
      (hBound.trans_lt (len_of_get hEvent)) hEvent
  · exact fun hRow col => lane.probabilityWeightOfLaunch hp hY hFrame hb hLo hHi col hRow

end PTX.Kernels.TmlFa4Fwd.Softmax
