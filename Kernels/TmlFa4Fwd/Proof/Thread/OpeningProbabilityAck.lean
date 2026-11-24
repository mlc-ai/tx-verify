-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityJoin
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningWaitHistory
public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditGate
import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import all Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The first probability acknowledgement and its actual local continuation. The acknowledgement
is the successful poll at pc 4874. -/
structure OpeningProbabilityAck (l : Launch) (X : Execution) (g : Nat) where
  index : Nat
  before : TState
  state : TState
  ending : Option TState
  acquired : Thread.Scores.CreditAcquired X (g,index)
  site : ∃ loc parity, X.get (g,index) = some ⟨4874,.wait loc parity true true .cta⟩
  bounded : index+1 ≤ (X.tr g).length
  released : index+1 = (X.tr g).length → Step.Released l X g
  ready : At state 4877 []
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some before)
  continuing : Run kernel Assumptions.all l g before ((X.tr g).drop (index+1)) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before state

  tensors : ((X.tr g).take (index+1)).countP isTcColl = 11

/-- A returned first statistics credit advances the opening publication.
At a suspended first acknowledgement the real poll count also bounds the
object phase, so a second transition cannot mask the returned credit. -/
theorem OpeningProbabilityJoin.acknowledgeOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads) {warp : Fin 8}
    (hw : warp.val = warpIndex l g) (c : OpeningProbabilityJoin l X g warp)
    (hAdvanced : let log := X.objects (Correction.statsCreditLoc l (g/l.block) (stageOf warp))
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ 1 ≤ s.phase) :
    Nonempty (OpeningProbabilityAck l X g) := by
  let stage := stageOf warp
  let offset := 8 * stage.val
  let F := firstAckAfterProb l offset none
  have hStage : warpIndex l g/4 = stage.val := by rw [← hw]; rfl
  have hObject : waitLoc l g stage 3 = Correction.statsCreditLoc l (g/l.block) stage := rfl
  have ht : At c.state 4868 (tailCarry l warp .first none) := c.ready
  obtain ⟨u,hLocal,hu⟩ := ((firstAckStage l g warp none).comp
    (firstAckAddress hp g offset (by have := stage.isLt; omega) none)).rtg ht
  have hBounded (s : MBarrier.State)
      (hs : MBarrier.stateBefore (X.objects (waitLoc l g stage 3))
        (X.objects (waitLoc l g stage 3)).length = some s)
      {v w : TState} (hr : Run kernel Assumptions.all l g {} (X.tr g) (some v))
      (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) v w) (hw : At w 4874 F) :
      s.phase ≤ 1 := by
    rw [hObject] at hs
    have hPoll := Protocol.Statistics.creditFinalPhaseLeSuccessfulPolls hp hMax.1 hCuQ hg
      stage hStage hs
    have hCursor := Correction.statsCreditPollCursor hp hMax.1 (j := (X.tr g).length)
      (g := g) stage hStage.symm
    rw [List.take_length] at hCursor
    exact hPoll.trans (hCursor.trans_le (atMostOneCreditAtOpeningAck hr hl hw.1))
  have hReady {s v : TState} (hr : Run kernel Assumptions.all l g {} (X.tr g) (some s))
      (hl : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s v) (ht : At v 4874 F) :
      let log := X.objects (waitLoc l g stage 3)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ 0%2 := by
    rw [← hObject] at hAdvanced
    obtain ⟨s,hs,hLo⟩ := hAdvanced
    have hHi := hBounded s hs hr hl ht
    exact ⟨s,hs,by omega⟩
  obtain ⟨n,after,v,he,hPast,hTail,hSteps,hV,hTensors⟩ :=
    waitOfMaximalWithTcCount hp hMax hg stage 3
    (phase := 0) (by decide) (F := F)
    (by
      intro pair hm
      simp only [F,firstAckAfterProb,firstAckCarry,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl
      · change (3948 : Nat) ≠ 9753; decide
      · change (3949 : Nat) ≠ 9753; decide)
    (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _))
    hReady c.positive c.bounded c.released hu c.recorded c.continuing
    (c.localSteps.trans hLocal)
  have hAcquired : Thread.Scores.CreditAcquired X (g,c.index+n) :=
    creditAcquiredOfObservation he rfl
  exact ⟨⟨c.index+n,after,v,c.ending,hAcquired,⟨_,_,he⟩,len_of_get he,
    releasedIfLast he (by simp [Kind.resume]),hV.mono trivial,hPast,hTail,hSteps,
    hTensors.trans c.tensors⟩⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
