-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityStatistics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedProbabilityFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityStoreValue
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Kernels.TmlFa4Fwd.Softmax

/-- The actual repeated continuation of a coefficient write, with its living
scores, affine inputs and probability-address registers. -/
def RepeatedProbabilityAfterCoefficient (p : Params) (l : Launch) (X : Execution)
    (mode : Repeated) (g pos : Nat) : Prop :=
  ∃ (stage : Fin 2) (t : TState) (ending : Option TState)
      (scores : Nat → Option ℝ) (reference : ℝ),
    Nonempty (RepeatedProbabilityShiftFrame p l mode g stage t scores reference) ∧
    Run kernel Assumptions.all l g t ((X.tr g).drop (pos+2)) ending

/-- The probability store belongs to this repeated body. -/
def RepeatedProbabilityStore (X : Execution) (mode : Repeated) (store : EvId) : Prop :=
  ∃ (q : Fin 4) (address : Nat) (vals : List Value) (shape : TcShape),
    X.get store = some ⟨probabilityPc mode.round q,.tc (.st address vals shape)⟩

/-- The actual coefficient frame and visit index reconstruct the repeated store's packed
words, with no requirement on the lane's events after that store. -/
theorem repeatedProbabilityPackedOfCoefficient {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (mode : Repeated)
    (hFrame : ∀ g pos a data,
      StatisticsStore X (g,pos) (rescaleStore (decide (mode = .biased))) a data →
      pos+2 < (X.tr g).length → RepeatedProbabilityAfterCoefficient p l X mode g pos)
    {store : EvId} (hStore : RepeatedProbabilityStore X mode store) :
    ∃ (address : Nat) (shape : TcShape) (weights : Nat → ℝ),
      X.TSt store address ((List.range 16).map (probabilityWord weights)) shape := by
  obtain ⟨g,index⟩ := store
  obtain ⟨q,address,vals,shape,he⟩ := hStore
  have hPosition :
      ∃ pos a data, StatisticsStore X (g,pos) (rescaleStore (decide (mode = .biased))) a data ∧
        index = pos+2+mode.probabilityStoreOffset q := by
    cases mode
    · exact biasedProbabilityCoefficientPosition hp hX q he
    · exact plainProbabilityCoefficientPosition hp hX q he
  obtain ⟨pos,a,data,hWrite,hIndex⟩ := hPosition
  have hBound : pos+2+mode.probabilityStoreOffset q < (X.tr g).length := by
    rw [← hIndex]
    exact len_of_get he
  have hPresent : pos+2 < (X.tr g).length := by omega
  obtain ⟨stage,t,ending,scores,reference,⟨frame⟩,hTail⟩ := hFrame g pos a data hWrite hPresent
  have hReplay := frame.storeOfPrefix hp hTail q (.inr hBound)
  rw [← hIndex] at hReplay
  let weights (col : Nat) := repeatedExpWeight
    (affineScore (abiFloat p.scaleLog2Bits) (-reference) (scores col))
  have hKind := congrArg Event.kind (Option.some.inj (he.symm.trans hReplay))
  obtain ⟨_,hPack,_⟩ := TcKind.st.inj (Kind.tc.inj hKind)
  refine ⟨address,shape,fun col => weights (32*q.val+col),probabilityPc mode.round q,?_⟩
  have hWords : vals = (List.range 16).map (probabilityWord (fun k => weights (32*q.val+k))) := by
    change vals = (List.range' (16*q.val) 16).map (probabilityWord weights) at hPack
    rw [hPack,List.range'_eq_map_range,List.map_map]
    apply List.map_congr_left
    intro k _
    unfold Function.comp probabilityWord
    rw [show 2*(16*q.val+k) = 32*q.val+2*k by omega,
      show 32*q.val+2*k+1 = 32*q.val+(2*k+1) by omega]
  exact hWords ▸ he

/-- A cell in the probability tile outside the opening publication belongs
to exactly one of the two repeated-body store families. -/
theorem laterProbabilityStoreOfCell {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {cell : TcMma.Cell} {stage : Fin 2}
    (hCell : TcMma.StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.probability stage))
    (hLater : ¬ OpeningProbabilityStore X store) :
    ∃ mode, RepeatedProbabilityStore X mode store := by
  obtain ⟨address,vals,shape,_,⟨pc,he⟩,_,_⟩ := hCell
  have hWarpGroup : store.1%l.block/128 = stage.val := hFoot.warpGroup
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨other,chunk,rfl⟩
  · cases round
    case first => exact (hLater ⟨q,address,vals,shape,he⟩).elim
    case unbiased => exact ⟨.unbiased,q,address,vals,shape,he⟩
    case biased => exact ⟨.biased,q,address,vals,shape,he⟩
  · have hCorrection := correctionStoreWarpGroup hp hX other chunk he
    rw [hCorrection] at hWarpGroup
    exact (Nat.ne_of_lt stage.isLt hWarpGroup.symm).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
