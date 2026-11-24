-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityStores
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.SoftmaxSignals
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.DrainInOrder
import Lemmas.Step.Object
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof AsyncCopy

/-- The opening main P packet returns from its three-store wait in the issuing lane. -/
structure OpeningProbabilityStoreWaitCursor (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  stored : OpeningProbabilityStoreCursor p l X g stage 2
  waited : X.get (g,stored.wait.statistics.index+5) =
    some ⟨probabilityWaitPc .first false,.tc .waitSt⟩
  ordinal : X.TcK (g,stored.wait.statistics.index+5) 8
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (stored.wait.statistics.index+6)) (some (next stored.state))
  continuation : Run kernel Assumptions.all l g (next stored.state)
    ((X.tr g).drop (stored.wait.statistics.index+6)) stored.wait.statistics.ending

/-- The third opening P store has all its peers and can reach the actual main wait. -/
theorem OpeningProbabilityStoreCursor.waitOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2}
    (c : OpeningProbabilityStoreCursor p l X g stage 2)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 7) :
    Nonempty (OpeningProbabilityStoreWaitCursor p l X g stage) := by
  let j := c.wait.statistics.index
  obtain ⟨site,he⟩ := c.stored
  have hBound : j+5 ≤ (X.tr g).length := len_of_get he
  have hReady (hEnd : j+5 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,probabilityCollectiveReleased he (.inr (.inr ⟨_,_,_,rfl⟩)) c.ordinal.2 hPeers hEnd⟩
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hPc : c.state.pc = 4845 := c.ready.1
  have hOut : out kernel Assumptions.all l g c.state = .ev (.tc .waitSt (next c.state)) := by
    rw [out_event c.ready.2.2.2.1 (hPc.symm ▸ Flow.code_4845) rfl rfl]
    simp [eventTmpl,tcTmpl,ofExec,hBlock,pure,Except.pure]
  obtain ⟨hWait,hPast,hRun⟩ := probabilityCollectiveOfMaximal hg (by omega) hBound
    hOut rfl nofun c.recorded .refl c.continuation hReady
  have hRecord : X.get (g,j+5) = some ⟨probabilityWaitPc .first false,.tc .waitSt⟩ := by
    change X.get (g,j+5) = some ⟨4845,.tc .waitSt⟩
    rwa [hPc] at hWait
  have hCount : ((X.tr g).take (j+5)).countP isTcColl = 8 := by
    change ((X.tr g).take (c.wait.statistics.index+2+(2 : Fin 3).val+1)).countP isTcColl = 8
    rw [countP_take_succ (p := isTcColl) he rfl,c.ordinal.2]
    rfl
  exact ⟨⟨c,hRecord,⟨⟨_,hRecord,rfl⟩,hCount⟩,hPast,hRun⟩⟩

/-- The actual main probability credit with the live tail-pack operand frame. -/
structure OpeningProbabilityCreditCursor (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  main : OpeningProbabilityStoreWaitCursor p l X g stage
  state : TState
  credited : Thread.Scores.ProbabilityCredit l X (g,main.stored.wait.statistics.index+6)
    (g/l.block) stage 0
  ordinal : ((X.tr g).take (main.stored.wait.statistics.index+7)).countP isTcColl = 9
  ready : At state (firstUnpackPc 3) []
  address : state.regs (probabilityReg .first 3) = some (b32 (probabilityAddress l g stage 3))
  packed : ∀ i < 8, state.regs (firstPackedReg 3+i) =
    some (probabilityDoubleWord (fun k => main.stored.wait.values (32*3+k)) i)
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (main.stored.wait.statistics.index+7)) (some state)
  continuation : Run kernel Assumptions.all l g state
    ((X.tr g).drop (main.stored.wait.statistics.index+7)) main.stored.wait.statistics.ending

/-- After the main P wait returns, the lane contributes a unit credit to the stage object. -/
theorem OpeningProbabilityStoreWaitCursor.creditCursorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2}
    (c : OpeningProbabilityStoreWaitCursor p l X g stage)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 8) :
    ∃ u : OpeningProbabilityCreditCursor p l X g stage, u.main = c := by
  let j := c.stored.wait.statistics.index
  let t := next c.stored.state
  let v := next (setReg t 3927 (b32 1))
  let addr := signalLoc l g stage 1
  let u := next (mbarStateDest v (some 8186))
  have ht : At t 4846 [] := c.stored.ready.next
  have hLocal : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local Flow.code_4846 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil
      (by rw [ht.1]; decide) rfl]
    rfl
  have hV : At v 4847 [(3927,b32 1)] := ht.set (by simp)
  have hBase : v.regs 3217 = some (b32 (l.sharedBase+8*stage.val)) := by
    simpa [v,t,next,setReg] using c.stored.frame
  have hOut : out kernel Assumptions.all l g v = .ev (.arrive addr 0 u 1 true .cta) :=
    signalTemplate hp stage 1 hV.1 hV.2.2.2.1 hBase hV.2.2.2.2.1
  let event := Event.mk v.pc (.arrive addr 0 1 true .cta)
  have hStep : EStep kernel Assumptions.all l g v event (some u) := ⟨_,hOut,rfl,rfl⟩
  have hBound : j+6 ≤ (X.tr g).length := len_of_get c.waited
  have hLt : j+6 < (X.tr g).length := by
    by_contra! hShort
    have hEq := Nat.le_antisymm hBound hShort
    have hReleased := probabilityCollectiveReleased c.waited (.inr (.inl rfl))
      c.ordinal.2 hPeers hEq
    have hStarted : X.tr g ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hBefore : Run kernel Assumptions.all l g {} (X.tr g) (some t) := by
      have hLen : (X.tr g).length ≤ c.stored.wait.statistics.index+6 := hShort
      simpa only [List.take_of_length_le hLen] using c.recorded
    apply hMax.not_grows
    refine Step.object_counted_extension_silent hMax.1 (by trivial) hg (.inl hStarted)
      hReleased hBefore (run_rtg hLocal) hStep ⟨trivial,fun _ h => by cases h⟩ (by trivial)
      (fun _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ _ _ _ _ h => by cases h) rfl (mb := addr) (act := .arrive 1 0)
      (fun _ _ h => by cases h) ?_ ?_
    · intro loc
      by_cases h : loc = addr
      · subst loc
        simp [objectAction,snoc_get_new,event]
      · simp [objectAction,snoc_get_new,event,h,Ne.symm h]
    · intro rec
      exact Assumptions.wfStep.quiet hMax.1
        (Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)) rfl
          ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
            (Execution.noNewRead_of_tr rfl))
  have hn : Next kernel Assumptions.all l g t v (.arrive addr 0 u 1 true .cta) :=
    ⟨run_rtg hLocal,hOut⟩
  obtain ⟨_,_,he,⟨rfl,hEnd⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,h⟩; cases h) c.continuation
    (fun hNil => (Nat.not_le_of_lt hLt) (List.drop_eq_nil_iff.mp hNil))
  have hLoc : addr = Thread.Scores.probabilityObject l (g/l.block) stage 0 := by
    change Loc.mk .shared (g/l.block) (l.sharedBase+8*stage.val+96) =
      Loc.mk .shared (g/l.block) (l.sharedBase+(96+8*stage.val+0))
    congr 1
    omega
  obtain rfl := Option.some.inj hEnd
  have hPub : Thread.Scores.ProbabilityCredit l X (g,j+6) (g/l.block) stage 0 :=
    ⟨_,by rwa [hLoc] at he⟩
  have hPast : Run kernel Assumptions.all l g {} ((X.tr g).take (j+7)) (some u) := by
    change Run kernel Assumptions.all l g {} ((X.tr g).take ((j+6)+1)) (some u)
    rw [List.take_add_one,show (X.tr g)[j+6]? = some event from he]
    exact c.recorded.snoc (run_rtg hLocal) hStep
  have hControl : ((X.tr g).take (j+7)).countP isTcColl = 9 := by
    change ((X.tr g).take ((j+6)+1)).countP isTcColl = 9
    rw [countP_take_succ_false (p := isTcColl) he rfl]
    change ((X.tr g).take ((j+5)+1)).countP isTcColl = 9
    rw [countP_take_succ (p := isTcColl) c.waited rfl,c.ordinal.2]
  have hU : At u (firstUnpackPc 3) [] :=
    ⟨congrArg (·+1) hV.1,hV.2.1,hV.2.2.1,hV.2.2.2.1,trivial⟩
  have hFrame (r : Nat) (hCount : r ≠ 3927) (hState : r ≠ 8186) :
      u.regs r = c.stored.state.regs r :=
    by simp [u,v,t,mbarStateDest,next,setReg,Function.update_of_ne hCount,
      Function.update_of_ne hState]
  refine ⟨⟨c,u,hPub,hControl,hU,?_,?_,hPast,hTail⟩,rfl⟩
  · exact (hFrame _ (by decide) (by decide)).trans (c.stored.addresses 3)
  · intro word hw
    have hReg : firstPackedReg 3 = 8178 := rfl
    exact (hFrame _ (by omega) (by omega)).trans (c.stored.packed 3 word hw)

/-- After the main P wait returns, the lane contributes a unit credit to the stage object. -/
theorem OpeningProbabilityStoreWaitCursor.creditOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2}
    (c : OpeningProbabilityStoreWaitCursor p l X g stage)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 8) :
    Thread.Scores.ProbabilityCredit l X (g,c.stored.wait.statistics.index+6)
      (g/l.block) stage 0 := by
  obtain ⟨after,hMain⟩ := c.creditCursorOfMaximal hp hMax hg hPeers
  simpa only [hMain] using after.credited


end PTX.Kernels.TmlFa4Fwd.Softmax
