-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityReplay
import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstStore
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- A prefix after one of the three opening probability stores before publication. -/
structure OpeningProbabilityStoreCursor (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) (quarter : Fin 3) where
  wait : OpeningProbabilityWaitCursor p l X g stage
  state : TState
  stored : X.TSt (g,wait.statistics.index+2+quarter.val)
    (probabilityAddress l g stage ⟨quarter.val,quarter.isLt.trans (by decide)⟩)
    ((List.range 16).map (probabilityWord (fun k => wait.values (32*quarter.val+k)))) .s32x32b
  ordinal : X.TcK (g,wait.statistics.index+2+quarter.val) (5+quarter.val)
  ready : At state (probabilityPc .first ⟨quarter.val,quarter.isLt.trans (by decide)⟩+1) []
  frame : state.regs 3217 = some (b32 (l.sharedBase+8*stage.val))
  addresses : ∀ q : Fin 4, state.regs (probabilityReg .first q) =
    some (b32 (probabilityAddress l g stage q))
  packed : ∀ q : Fin 4, ∀ i < 8, state.regs (firstPackedReg q+i) =
    some (probabilityDoubleWord (fun k => wait.values (32*q.val+k)) i)
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (wait.statistics.index+3+quarter.val))
    (some state)
  continuation : Run kernel Assumptions.all l g state
    ((X.tr g).drop (wait.statistics.index+3+quarter.val)) wait.statistics.ending

/-- Every lane in the wait's warp is at the same Tensor Memory ordinal before the first store. -/
theorem OpeningProbabilityWaitCursor.firstStoreOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityWaitCursor p l X g stage)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 4) :
    Nonempty (OpeningProbabilityStoreCursor p l X g stage 0) := by
  let j := c.statistics.index
  have he : X.get (g,j+1) = some ⟨4826,.tc .waitLd⟩ := c.waited
  have hBound : j+2 ≤ (X.tr g).length := len_of_get he
  have hReady (hEnd : j+2 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,probabilityCollectiveReleased he (.inl rfl) c.ordinal.2 hPeers hEnd⟩
  have hOut := packedProbabilityStoreTemplate hp stage 0 c.values c.site c.fault c.sub
    (c.addresses 0) c.unpacked
  obtain ⟨hStore,hRecorded,hTail⟩ := probabilityCollectiveOfMaximal hg (by omega) hBound
    hOut rfl nofun c.recorded (.refl) c.continuation hReady
  have hs : X.get (g,j+2) = some ⟨probabilityPc .first 0,.tc (.st
      (probabilityAddress l g stage 0) ((List.range 16).map (probabilityWord c.values))
      .s32x32b)⟩ := c.site ▸ hStore
  have hCount : ((X.tr g).take (j+2)).countP isTcColl = 5 := by
    rw [countP_take_succ (p := isTcColl) he rfl,c.ordinal.2]
  let after := next {c.state with sub := 0}
  have hAt : At after (probabilityPc .first 0+1) [] :=
    ⟨congrArg (·+1) c.site,rfl,c.acc,c.fault,trivial⟩
  have hStore' : X.get (g,j+2) = some ⟨probabilityPc .first 0,.tc (.st
      (probabilityAddress l g stage 0)
      ((List.range 16).map (probabilityWord (fun k => c.values (32*(0 : Fin 3).val+k))))
      .s32x32b)⟩ := by simpa using hs
  exact ⟨⟨c,after,⟨_,hStore'⟩,⟨⟨_,hs,rfl⟩,hCount⟩,hAt,c.shared,c.addresses,c.packed,
    hRecorded,hTail⟩⟩

/-- Releasing a preceding opening store enables the next quarter of the same P packet. -/
theorem OpeningProbabilityStoreCursor.nextStoreOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (q : Fin 2)
    (c : OpeningProbabilityStoreCursor p l X g stage ⟨q.val,q.isLt.trans (by decide)⟩)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) (5+q.val)) :
    Nonempty (OpeningProbabilityStoreCursor p l X g stage ⟨q.val+1,by have := q.isLt; omega⟩) := by
  let old : Fin 4 := ⟨q.val,q.isLt.trans (by decide)⟩
  let new : Fin 4 := ⟨q.val+1,by have := q.isLt; omega⟩
  let values := fun k => c.wait.values (32*new.val+k)
  let j := c.wait.statistics.index
  let pos := j+3+q.val
  have hStart : At c.state (firstUnpackPc new) [] := by
    have hPc : probabilityPc .first old+1 = firstUnpackPc new := by fin_cases q <;> rfl
    exact hPc ▸ c.ready
  obtain ⟨v,hV,hLocal,hWords,hFrame⟩ :=
    probabilityUnpackLocal (g := g) new values hStart (c.packed new)
  have hOff (r : Nat) (hr : r ∈ [3217,3223,3224,3225,3226]) : r < firstUnpackBase new := by
    unfold firstUnpackBase
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    omega
  have hAddr (quarter : Fin 4) : v.regs (probabilityReg .first quarter) =
      some (b32 (probabilityAddress l g stage quarter)) :=
    (hFrame _ (.inl (hOff _ (by fin_cases quarter <;> decide)))).trans (c.addresses quarter)
  have hSub : v.sub = if delayedProbability .first new then 1 else 0 := by
    have hDelay : delayedProbability .first new = false := by fin_cases q <;> rfl
    rw [hDelay]
    exact hV.2.1
  have hOut := packedProbabilityStoreTemplate hp stage new values hV.1 hV.2.2.2.1 hSub
    (hAddr new) hWords
  obtain ⟨site,he⟩ := c.stored
  have hAfter : j+2+q.val+1 = pos := by dsimp [pos]; omega
  have hBound : pos ≤ (X.tr g).length := hAfter ▸ len_of_get he
  have hReleased (hLast : pos = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,probabilityCollectiveReleased he (.inr (.inr ⟨_,_,_,rfl⟩)) c.ordinal.2 hPeers
      (hAfter.trans hLast)⟩
  obtain ⟨heStore,hPrefix,hTail⟩ := probabilityCollectiveOfMaximal hg
    (show 0 < pos by dsimp [pos]; omega) hBound hOut rfl nofun
    c.recorded hLocal c.continuation hReleased
  have hStore : X.get (g,pos) = some ⟨probabilityPc .first new,.tc (.st
      (probabilityAddress l g stage new) ((List.range 16).map (probabilityWord values))
      .s32x32b)⟩ :=
    hV.1 ▸ heStore
  have hPosition : pos = j+2+(q.val+1) := by dsimp [pos]; omega
  have hCount : ((X.tr g).take pos).countP isTcColl = 5+(q.val+1) := by
    rw [← hAfter,countP_take_succ (p := isTcColl) he rfl,c.ordinal.2]
    change 5+q.val+1 = 5+(q.val+1)
    omega
  let after := next {v with sub := 0}
  have hAt : At after (probabilityPc .first new+1) [] :=
    ⟨congrArg (·+1) hV.1,rfl,hV.2.2.1,hV.2.2.2.1,trivial⟩
  have hPrefixPos : pos+1 = j+3+(q.val+1) := by dsimp [pos]; omega
  refine ⟨⟨c.wait,after,⟨_,hPosition ▸ hStore⟩,⟨⟨_,hPosition ▸ hStore,rfl⟩,hPosition ▸ hCount⟩,
    hAt,(hFrame 3217 (.inl (hOff 3217 (by simp)))).trans c.frame,hAddr,?_,
    hPrefixPos ▸ hPrefix,hPrefixPos ▸ hTail⟩⟩
  intro quarter i hi
  have hRange : firstUnpackBase new+16 ≤ firstPackedReg quarter+i := by
    unfold firstUnpackBase firstPackedReg
    have hn := new.isLt
    have hExtra : (if new.val = 3 then 1 else 0) ≤ 1 := by split <;> omega
    omega
  exact (hFrame _ (.inr hRange)).trans (c.packed quarter i hi)

end PTX.Kernels.TmlFa4Fwd.Softmax
