-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainScoreEntry
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPlainScoreEntry
public import Kernels.TmlFa4Fwd.Proof.SoftmaxUnbiasedProbabilityAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningScore
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreReadyUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- A successful repeated score acquire and the recorded cursor for its first score load. -/
structure RepeatedScoreCursor (l : Launch) (X : Execution) (g : Nat) (round : Round)
    (stage : Fin 2) (phase : Nat) (F : List (Nat × Value)) where
  cursor : OpeningTripCursor l X g (scorePc round 0) F
  index : Nat
  position : cursor.pos = index+1
  acquired : X.get (g,index) =
    some ⟨(waitSite (qkWaitSite round)).pc,
      .wait (Thread.Scores.scoreReadyObject l (g/l.block) stage) phase true true .cta⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (round : Round)
    (stage : Fin 2) (phase : Nat) (hPhase : phase < 2) {F : List (Nat × Value)}
    (hBase : ((waitSite (qkWaitSite round)).base,
      b32 (waitLoc l g stage (qkWaitSite round)).addr) ∈ F)
    (hPar : ((waitSite (qkWaitSite round)).phase,b32 phase) ∈ F)
    (hFresh : ∀ x ∈ F, x.1 ≠ (waitSite (qkWaitSite round)).result)
include hp hMax hg round stage phase hPhase hBase hPar hFresh

theorem scoreReturnAtWaitOfPending (c : OpeningTripCursor l X g (waitSite (qkWaitSite round)).pc F)
    (hReady : let loc := Thread.Scores.scoreReadyObject l (g/l.block) stage
      okPolls loc (X.tr g) = okPolls loc ((X.tr g).take c.pos) →
      OpeningPollReady X (Thread.Scores.scoreReadyObject l (g/l.block) stage) phase) :
    ∃ u : RepeatedScoreCursor l X g round stage phase F, c.pos ≤ u.index ∧
      u.cursor.ending = c.ending ∧
      (X.tr g).drop c.pos = List.replicate (u.index-c.pos)
        ⟨(waitSite (qkWaitSite round)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) stage) phase false true .cta⟩ ++
        ⟨(waitSite (qkWaitSite round)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) stage) phase true true .cta⟩ ::
          (X.tr g).drop u.cursor.pos := by
  have hObject : waitLoc l g stage (qkWaitSite round) =
      Thread.Scores.scoreReadyObject l (g/l.block) stage := by cases round <;> rfl
  obtain ⟨n,after,v,hEvent,hPrefix,hTail,hLocal,hAt,hPolls⟩ :=
    waitAtCountOfMaximalWithTrace hp hMax hg stage (qkWaitSite round) hPhase hFresh hBase hPar
      (okPoll (waitLoc l g stage (qkWaitSite round))) rfl _
      (fun hEq {_ _} _ _ _ => by rw [hObject] at hEq ⊢; exact hReady hEq) rfl
      c.positive c.bounded c.released c.checkpoint c.recorded c.remaining c.localSteps
  have hNext : (waitSite (qkWaitSite round)).pc+3 = scorePc round 0 := by cases round <;> rfl
  have hBound : c.pos+n+1 ≤ (X.tr g).length := len_of_get hEvent
  have hRelease : c.pos+n+1 = (X.tr g).length → Step.Released l X g :=
    Prologue.releasedIfLast hEvent (by intro h; cases h)
  have hPositive : 0 < c.pos+n+1 := Nat.succ_pos _
  have hAcquire := hEvent
  rw [hObject] at hAcquire
  refine ⟨⟨⟨c.pos+n+1,after,v,c.ending,hPositive,hBound,hRelease,hNext ▸ hAt,hPrefix,hTail,
    hLocal⟩,c.pos+n,rfl,hAcquire⟩,Nat.le_add_right _ _,rfl,?_⟩
  simpa only [Nat.add_sub_cancel_left,hObject] using hPolls

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (phase : Nat) (hPhase : phase < 2) (facts : List (Nat × Value))
    (hStable : ∀ x ∈ facts, x.1 ∉ unbiasedSetupWrites) (hFresh : ∀ x ∈ facts, x.1 ≠ 9821)
    (c : OpeningTripCursor l X g 6661
      ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 phase)::facts))
include hp hMax hg warp phase hPhase facts hStable hFresh c

/-- Once the stage's score is ready, the real plain-loop head polls successfully
and reaches the first TMEM score load with its live frame. -/
theorem plainScoreReturnOfPending
    (hReady : let loc := Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp)
      okPolls loc (X.tr g) = okPolls loc ((X.tr g).take c.pos) →
      OpeningPollReady X
      (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp)) phase) :
    ∃ u : RepeatedScoreCursor l X g .unbiased (stageOf warp) phase
        (plainReadyFacts l g warp phase facts),
      c.pos ≤ u.index ∧ u.cursor.ending = c.ending ∧
      (X.tr g).drop c.pos = List.replicate (u.index-c.pos)
        ⟨(waitSite (qkWaitSite .unbiased)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp))
            phase false true .cta⟩ ++
        ⟨(waitSite (qkWaitSite .unbiased)).pc,
          .wait (Thread.Scores.scoreReadyObject l (g/l.block) (stageOf warp))
            phase true true .cta⟩ :: (X.tr g).drop u.cursor.pos := by
  obtain ⟨s,hs,hLocal⟩ := plainScoreReadyLocal hp warp facts hStable c.checkpoint
  exact scoreReturnAtWaitOfPending hp hMax hg .unbiased (stageOf warp) phase hPhase
    (.head _) (.tail _ (.tail _ (.head _))) (plainReadyScratch hFresh)
    ⟨c.pos,c.before,s,c.ending,c.positive,c.bounded,c.released,hs,c.recorded,c.remaining,
      c.localSteps.trans hLocal⟩ hReady

end PTX.Kernels.TmlFa4Fwd.Softmax
