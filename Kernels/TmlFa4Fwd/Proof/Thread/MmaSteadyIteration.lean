-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyBodyEnd
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyRoots

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Mma (ReleaseIssue)

noncomputable section

/-- One pending MMA visit with the actual loop counter and the retained opening ABI. -/
abbrev SteadyIterationCursor (l : Launch) (X : Execution)
    (g visit remaining shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2291
    (fun _ => steadyFrame l visit remaining ++ steadyIterationRoots l) shuffles votes ends

/-- Producer phases required by one recurring visit. -/
structure SteadyIterationPhases (l : Launch) (X : Execution) (cta visit : Nat) : Prop where
  valuePhase : MmaProgressPhase X ⟨.shared,cta,readyAddr l (2*visit+1)⟩ (readyWord (2*visit+1))
  keyPhase : MmaProgressPhase X ⟨.shared,cta,readyAddr l (2*visit+2)⟩ (readyWord (2*visit+2))
  probabilityMain : ∀ stage : Fin 2,
    MmaProgressPhase X (Thread.Scores.probabilityObject l cta stage 0) (visit%2)
  probabilityTail : ∀ stage : Fin 2,
    MmaProgressPhase X (Thread.Scores.probabilityObject l cta stage 1) (visit%2)

/-- The barrier must enable a poll only when the actual trace has reached its frontier,
still carrying this visit's counter, phase and ring projection. -/
def SteadyPollFrontier (l : Launch) (X : Execution) (g visit remaining : Nat)
    (site : Fin 14) (object : Loc) (parity : Nat) : Prop :=
  ∀ lane < 32, ∀ {t u},
    Run kernel Assumptions.all l (warpLane l g lane) {} (X.tr (warpLane l g lane)) (some t) →
    Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) t u →
    At u (waitSite site).pc (steadyFrame l visit remaining) → MmaProgressPhase X object parity

/-- The six conditional waits of a recurring visit. Later ready generations can
coexist with earlier visits that already recorded the corresponding successful poll. -/
structure SteadyIterationFrontiers (l : Launch) (X : Execution)
    (g visit remaining : Nat) : Prop where
  valuePhase : SteadyPollFrontier l X g visit remaining 3
    ⟨.shared,g/l.block,readyAddr l (2*visit+1)⟩ (readyWord (2*visit+1))
  keyPhase : SteadyPollFrontier l X g visit remaining 6
    ⟨.shared,g/l.block,readyAddr l (2*visit+2)⟩ (readyWord (2*visit+2))
  probabilityMain : ∀ stage : Fin 2,
    SteadyPollFrontier l X g visit remaining (if stage = 0 then 4 else 7)
      (Thread.Scores.probabilityObject l (g/l.block) stage 0) (visit%2)
  probabilityTail : ∀ stage : Fin 2,
    SteadyPollFrontier l X g visit remaining (if stage = 0 then 5 else 8)
      (Thread.Scores.probabilityObject l (g/l.block) stage 1) (visit%2)

/-- Each completed recurring visit issues both probability products, both next score
notifications, and the releases for its current K and V slots. -/
structure SteadyIterationIssues (l : Launch) (X : Execution) (g visit : Nat) : Prop where
  probabilityProducts : ∀ stage : Fin 2,
    PvPacketIssues l X g ⟨stage.val,stage.isLt.trans (by decide)⟩
      (2*visit+1) (decide (0<visit))
  scoreNotifications : ∀ stage : Fin 2, ∃ issuer idx, SameWarp l g issuer ∧
    X.Commit (issuer,idx) (commitSpec l issuer (l.sharedBase+80+8*stage.val))
  valueRelease : ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopValue
    (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+1)).val+56))
  keyRelease : ∃ issuer idx, SameWarp l g issuer ∧ ReleaseIssue X issuer idx .loopKey
    (commitSpec l issuer (l.sharedBase+8*(readyStage (2*visit+2)).val+56))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

end
end PTX.Kernels.TmlFa4Fwd.Mma
