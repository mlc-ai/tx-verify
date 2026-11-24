-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasReturn
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- The scalar Bias reads, proxy fence, named arrival, and possible release have
not consumed a Tensor Memory collective instance. -/
theorem OpeningFmaLane.tensorCount {p : Params} {l : Launch} {X : Execution}
    {g batch wait : Nat} {stage : Fin 2} (lane : OpeningFmaLane p l X g batch stage wait) :
    ((X.tr g).take lane.pos).countP isTcColl = 4 := by
  have hStart := lane.arrival.loaded.opening.tensorCount
  rw [lane.arrival.loaded.opening.position] at hStart
  have hScalar : (((X.tr g).drop (wait+1)).take 64).countP isTcColl = 0 := by
    apply List.countP_eq_zero.mpr
    intro e hm
    obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hm
    have hN := (List.getElem?_eq_some_iff.mp hn).1
    simp only [List.length_take] at hN
    have hBound : n < 64 := by omega
    let i : Fin 16 := ⟨n/4,by omega⟩
    let k := n%4
    obtain ⟨bs,he,_⟩ := lane.arrival.loaded.words i k (Nat.mod_lt _ (by decide))
    rw [List.getElem?_take_of_lt hBound,List.getElem?_drop] at hn
    have hIndex : wait+1+4*i.val+k = wait+1+n := by dsimp [i,k]; omega
    rw [hIndex] at he
    change (X.tr g)[wait+1+n]? = some _ at he
    obtain rfl := Option.some.inj (hn.symm.trans he)
    simp [isTcColl]
  have hFence : ((X.tr g).take (wait+65)).countP isTcColl = 4 := by
    change ((X.tr g).take (wait+1+64)).countP isTcColl = 4
    rw [List.take_add,List.countP_append,hStart,hScalar]
  have hBar := (countP_take_succ_false lane.arrival.fence (p := isTcColl) rfl).trans hFence
  have hReturn := (countP_take_succ_false lane.arrival.arrival (p := isTcColl) rfl).trans hBar
  by_cases hLeader : laneOf l g = 0
  · rw [lane.position,ite_eq_left hLeader]
    exact (countP_take_succ_false (lane.releasedBias hLeader) (p := isTcColl) rfl).trans hReturn
  · rw [lane.position,ite_eq_right hLeader]
    exact hReturn

end PTX.Kernels.TmlFa4Fwd.Softmax
