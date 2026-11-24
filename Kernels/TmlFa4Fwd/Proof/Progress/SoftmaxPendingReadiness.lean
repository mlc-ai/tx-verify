-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxLoopTransitions
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaRecurringNotifications
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringScoreProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditGate
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.StatsCreditHistory
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax

/-- A delivered score notification of ordinal `visit` is ready for every lane of the stage
still waiting for its `visit`-th score. -/
theorem scoreReadyForPendingLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {g visit : Nat} (hw : warpIndex l g < 8)
    (stage : Fin 2) (hStage : warpIndex l g/4 = stage.val)
    (delivered : ∃ issue spec, Scores.ScoreCommit l X issue (g/l.block) stage spec 0 ∧
      Scores.scoreCommitOrdinal l X (g/l.block) stage issue = visit ∧
      (0 : Fin 16) ∈ X.tcNotified issue) :
    okPolls (Scores.scoreReadyObject l (g/l.block) stage) (X.tr g) = visit →
      OpeningPollReady X (Scores.scoreReadyObject l (g/l.block) stage) (visit%2) := by
  intro pending
  obtain ⟨issue,spec,commit,ord,done⟩ := delivered
  obtain ⟨s,hs,hPhase⟩ := Protocol.Scores.pendingScorePhaseOfNotification hp hMax.1
    (Protocol.Scores.correctionJointGuardsOfCuQ hp hMax.1 (frame.metadataProtected hp).1)
    hw stage hStage commit ord done pending
  exact ⟨s,hs,by rw [hPhase]; omega⟩

/-- A steady MMA iteration delivers the score of the next visit to both stages. -/
theorem scoreDeliveredOfAges {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {mma visit : Nat}
    (ages : Mma.SteadyRetirementAges l X mma visit) (stage : Fin 2) :
    ∃ issue spec, Scores.ScoreCommit l X issue (mma/l.block) stage spec 0 ∧
      Scores.scoreCommitOrdinal l X (mma/l.block) stage issue = visit+1 ∧
      (0 : Fin 16) ∈ X.tcNotified issue := by
  obtain ⟨issue,spec,_,commit,ord,done⟩ := deliveredRecurringScore hp hMax frame ages stage
  exact ⟨issue,spec,commit,ord,done⟩

/-- The correction credits of generation `visit` release a softmax lane of the stage that is
waiting for its acknowledgement of that visit, having acquired `visit+1` credits. -/
theorem ackReadyForPendingLane {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {g visit : Nat} (hg : g < l.threads)
    (stage : Fin 2) (hStage : warpIndex l g/4 = stage.val)
    (credits : Protocol.Statistics.TerminalCorrectionCredits l X (g/l.block) stage visit)
    (site : Fin 10) (hSite : waitLoc l g stage site =
      Correction.statsCreditLoc l (g/l.block) stage) :
    (X.tr g).countP Scores.creditAcquired = visit+1 →
      OpeningPollReady X (waitLoc l g stage site) (visit%2) := by
  intro pending
  obtain ⟨q,k⟩ := frame.metadataProtected hp
  have deps := Protocol.Statistics.creditDependenciesOfCountedExitBound hp hMax.1
    (Protocol.Statistics.countedExitCreditBound hp hMax.1 q k)
  obtain ⟨s,hs,hLo⟩ := Protocol.Statistics.statisticsPhaseAdvancedOfCredits hp hMax.1 deps
    stage credits
  have hHi := Protocol.Statistics.creditFinalPhaseLeSuccessfulPolls hp hMax.1 q hg stage hStage hs
  have hCursor := Correction.statsCreditPollCursor hp hMax.1 (j := (X.tr g).length)
    (g := g) stage hStage.symm
  rw [List.take_length,Scores.beforeCredits,List.take_length] at hCursor
  rw [hSite]
  refine ⟨s,hs,?_⟩
  have e : s.phase = visit+1 := by omega
  rw [e]
  omega

end PTX.Kernels.TmlFa4Fwd.Progress
