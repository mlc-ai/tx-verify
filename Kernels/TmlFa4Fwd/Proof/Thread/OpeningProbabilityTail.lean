-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityCredit
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

/-- The fourth opening store writes the separately published tail of the P row. -/
structure OpeningProbabilityTailStore (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  main : OpeningProbabilityCreditCursor p l X g stage
  state : TState
  stored : X.TSt (g,main.main.stored.wait.statistics.index+7) (probabilityAddress l g stage 3)
    ((List.range 16).map (probabilityWord (fun k => main.main.stored.wait.values (96+k)))) .s32x32b
  ordinal : X.TcK (g,main.main.stored.wait.statistics.index+7) 9
  ready : At state (probabilityWaitPc .first true) []
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (main.main.stored.wait.statistics.index+8)) (some state)
  continuation : Run kernel Assumptions.all l g state
    ((X.tr g).drop (main.main.stored.wait.statistics.index+8))
    main.main.stored.wait.statistics.ending

/-- The main credit does not block its lane's actual fourth probability store. -/
theorem OpeningProbabilityCreditCursor.tailStoreOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2}
    (c : OpeningProbabilityCreditCursor p l X g stage) :
    Nonempty (OpeningProbabilityTailStore p l X g stage) := by
  let j := c.main.stored.wait.statistics.index
  let values := fun k => c.main.stored.wait.values (96+k)
  obtain ⟨v,hV,hLocal,hWords,hFrame⟩ :=
    probabilityUnpackLocal (g := g) 3 values c.ready c.packed
  have hAddr := (hFrame (probabilityReg .first 3) (.inl (by decide))).trans c.address
  have hOut := packedProbabilityStoreTemplate hp stage 3 values hV.1 hV.2.2.2.1 hV.2.1 hAddr hWords
  obtain ⟨pc,he⟩ := c.credited
  have hBound : j+7 ≤ (X.tr g).length := len_of_get he
  have hReady (hEnd : j+7 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,Prologue.releasedIfLast he (by intro h; cases h) hEnd⟩
  obtain ⟨hs,hPast,hTail⟩ := probabilityCollectiveOfMaximal hg (by omega) hBound
    hOut rfl nofun c.recorded hLocal c.continuation hReady
  have hStore : X.get (g,j+7) = some ⟨probabilityPc .first 3,.tc (.st
      (probabilityAddress l g stage 3) ((List.range 16).map (probabilityWord values)) .s32x32b)⟩ :=
    hV.1 ▸ hs
  let after := next {v with sub := 0}
  have hAt : At after (probabilityWaitPc .first true) [] :=
    ⟨congrArg (·+1) hV.1,rfl,hV.2.2.1,hV.2.2.2.1,trivial⟩
  exact ⟨⟨c,after,⟨_,hStore⟩,⟨⟨_,hStore,rfl⟩,c.ordinal⟩,hAt,hPast,hTail⟩⟩

/-- The fourth probability store and its actual terminal store wait. -/
structure OpeningProbabilityTailWait (p : Params) (l : Launch) (X : Execution)
    (g : Nat) (stage : Fin 2) where
  tail : OpeningProbabilityTailStore p l X g stage
  waited : X.get (g,tail.main.main.stored.wait.statistics.index+8) =
    some ⟨probabilityWaitPc .first true,.tc .waitSt⟩
  ordinal : X.TcK (g,tail.main.main.stored.wait.statistics.index+8) 10
  recorded : Run kernel Assumptions.all l g {}
    ((X.tr g).take (tail.main.main.stored.wait.statistics.index+9)) (some (next tail.state))
  continuation : Run kernel Assumptions.all l g (next tail.state)
    ((X.tr g).drop (tail.main.main.stored.wait.statistics.index+9))
    tail.main.main.stored.wait.statistics.ending

/-- An aligned fourth store allows an actual tail store wait. -/
theorem OpeningProbabilityTailStore.waitOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {stage : Fin 2} (c : OpeningProbabilityTailStore p l X g stage)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) 9) :
    Nonempty (OpeningProbabilityTailWait p l X g stage) := by
  let j := c.main.main.stored.wait.statistics.index
  obtain ⟨pc,he⟩ := c.stored
  have hBound : j+8 ≤ (X.tr g).length := len_of_get he
  have hReady (hEnd : j+8 = (X.tr g).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g :=
    ⟨X,hMax,rfl,probabilityCollectiveReleased he (.inr (.inr ⟨_,_,_,rfl⟩)) c.ordinal.2 hPeers hEnd⟩
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hPc : c.state.pc = 4857 := c.ready.1
  have hOut : out kernel Assumptions.all l g c.state = .ev (.tc .waitSt (next c.state)) := by
    rw [out_event c.ready.2.2.2.1 (hPc.symm ▸ Flow.code_4857) rfl rfl]
    simp [eventTmpl,tcTmpl,ofExec,hBlock,pure,Except.pure]
  obtain ⟨hWait,hPast,hRun⟩ := probabilityCollectiveOfMaximal hg (by omega) hBound
    hOut rfl nofun c.recorded .refl c.continuation hReady
  have hRecord : X.get (g,j+8) = some ⟨probabilityWaitPc .first true,.tc .waitSt⟩ := by
    change X.get (g,j+8) = some ⟨4857,.tc .waitSt⟩
    rwa [hPc] at hWait
  have hCount : ((X.tr g).take (j+8)).countP isTcColl = 10 := by
    change ((X.tr g).take (c.main.main.stored.wait.statistics.index+7+1)).countP isTcColl = 10
    rw [countP_take_succ (p := isTcColl) he rfl,c.ordinal.2]
  exact ⟨⟨c,hRecord,⟨⟨_,hRecord,rfl⟩,hCount⟩,hPast,hRun⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
