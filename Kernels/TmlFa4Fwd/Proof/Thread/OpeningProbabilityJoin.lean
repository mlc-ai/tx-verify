-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTailCredit
import all Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityTailCredit
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Lemmas.Step.Object
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.EventCont
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue

/-- A lane at the opening probability publication join, with its actual trace cursor. -/
structure OpeningProbabilityJoin (l : Launch) (X : Execution) (g : Nat) (warp : Fin 8) where
  index : Nat
  before : TState
  state : TState
  ending : Option TState
  ready : At state 4868 (tailFrame l warp)
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take index) (some before)
  continuing : Run kernel Assumptions.all l g before ((X.tr g).drop index) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state
  positive : 0 < index
  bounded : index ≤ (X.tr g).length
  released : index = (X.tr g).length → Step.Released l X g

  tensors : ((X.tr g).take index).countP isTcColl = 11

/-- The selected lane records its credit and its peers take the decoded local bypass. -/
theorem OpeningProbabilityElection.joinOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (hRole : warpIndex l g/4 = stage.val)
    (c : OpeningProbabilityElection p l X g stage) :
    let warp : Fin 8 := ⟨warpIndex l g, by have := stage.isLt; omega⟩
    Nonempty (OpeningProbabilityJoin l X g warp) := by
  dsimp only
  let w : Fin 8 := ⟨warpIndex l g, by have := stage.isLt; omega⟩
  let pos := c.barrier.wait.tail.main.main.stored.wait.statistics.index+11
  let t := next (next c.barrier.wait.tail.state)
  let s := tailElectionReturn l g t c.leader
  let ending := c.barrier.wait.tail.main.main.stored.wait.statistics.ending
  let chosen := laneOf l g = c.leader
  have ht : At t 4859 [] := c.barrier.wait.tail.ready.next.next
  have hFrame := electionStartupFrame hp hMax hg c w rfl
  change Holds t.regs (tailFrame l w) at hFrame
  have hAt : At s 4860 ((623,.pred (decide chosen)) :: tailFrame l w) := by
    refine ⟨congrArg (·+1) ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,?_⟩
    simp [s,tailElectionReturn,next,setReg,chosen,tailFrame] at hFrame ⊢
    exact ⟨by by_cases h : laneOf l g = c.leader.val <;> simp [h], hFrame⟩
  obtain ⟨u,hLocal,hU⟩ := ((tailNegate l g .first w none false (decide chosen)).comp
    (tailBranch .first w none false (decide chosen))).rtg hAt
  change At u (if decide chosen = true then 4862 else 4868) (tailFrame l w) at hU
  have hBound : pos ≤ (X.tr g).length := len_of_get c.elected
  have hExitRelease (hEnd : pos = (X.tr g).length) : Step.Released l X g := by
    constructor
    intro _ _ _ _
    have hIndex : (X.tr g).length-1 =
        c.barrier.wait.tail.main.main.stored.wait.statistics.index+10 := by
          dsimp [pos] at hEnd
          omega
    rw [hIndex]
    exact elect_ready hMax.1 c.elected
  have tcount : ((X.tr g).take pos).countP isTcColl = 11 := by
    let j := c.barrier.wait.tail.main.main.stored.wait.statistics.index
    obtain ⟨_,bar⟩ := c.barrier.arrived
    change ((X.tr g).take (j+10+1)).countP isTcColl = 11
    rw [countP_take_succ_false c.elected rfl,countP_take_succ_false bar rfl,
      countP_take_succ c.barrier.wait.waited rfl,c.barrier.wait.ordinal.2]
  by_cases hLeader : chosen
  · have hNext : At u 4862 (tailFrame l w) := by
      simpa only [decide_eq_true_eq,ite_eq_left hLeader] using hU
    obtain ⟨v,hPrepare,hV⟩ := (tailPrepare hp g .first w none false).rtg hNext
    have hV' : At v 4867
        (((signalSite 2).base,b32 (l.sharedBase+8*(stageOf w).val)) ::
          ((signalSite 2).count,b32 1) :: tailFrame l w) := hV
    let loc := signalLoc l g (stageOf w) 2
    let nextState := next (mbarStateDest v (some (signalSite 2).state))
    have hTemplate := signalTemplate hp (stageOf w) 2 (g := g) hV'.1 hV'.2.2.2.1 hV'.2.2.2.2.1
      hV'.2.2.2.2.2.1
    have hn : Next kernel Assumptions.all l g s v (.arrive loc 0 nextState 1 true .cta) :=
      ⟨hLocal.trans hPrepare,hTemplate⟩
    obtain ⟨atSite,hCredit⟩ := c.creditAtElectionOfMaximal hp hMax hg hRole hLeader
    have hRoom : pos < (X.tr g).length := len_of_get hCredit
    obtain ⟨_,_,hEvent,⟨rfl,hAfter⟩,hTail⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,hBad⟩; cases hBad) c.continuation
      (fun hNil => Nat.not_le_of_lt hRoom (List.drop_eq_nil_iff.mp hNil))
    obtain rfl := Option.some.inj hAfter
    have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some nextState) := by
      rw [List.take_add_one,show (X.tr g)[pos]? = _ from hEvent]
      exact c.recorded.snoc hn.steps ⟨_,hTemplate,rfl,rfl⟩
    have hAt : At nextState 4868 (tailFrame l w) := by
      refine ⟨congrArg (·+1) hV'.1,hV'.2.1,hV'.2.2.1,hV'.2.2.2.1,?_⟩
      exact holds_update hV'.2.2.2.2.2.2 (by
        intro pair hm
        simp only [tailFrame,List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl
        · change (1062 : Nat) ≠ (signalSite 2).state; decide
        · change (2535 : Nat) ≠ (signalSite 2).state; decide)
    exact ⟨⟨pos+1,nextState,nextState,ending,hAt,hPast,hTail,.refl,by omega,hRoom,
      releasedIfLast hEvent (by intro h; cases h),by rwa [countP_take_succ_false hEvent rfl]⟩⟩
  · have hAt : At u 4868 (tailFrame l w) := by
      simpa only [decide_eq_true_eq,ite_eq_right hLeader] using hU
    exact ⟨⟨pos,s,u,ending,hAt,c.recorded,c.continuation,hLocal,by dsimp [pos]; omega,
      hBound,hExitRelease,tcount⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
