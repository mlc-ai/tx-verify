-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MbarUpdateFamily
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderEmptyFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryEmptyFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReuseClosure
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsCreditFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCompletion
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputFree
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import Kernels.TmlFa4Fwd.Proof.Protocol.SoftmaxProbabilityReuse
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasNotificationFaults
import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringScoreGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy PTX.MBarrier Thread

/-- Actual counter updates of every mbarrier are clean with the launch offsets preserved. -/
theorem mbarUpdatesClean {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc)
    (hUpdate : (∃ count tx, r.action = .arrive count tx) ∨ ∃ bytes, r.action = .completeTx bytes) :
    r.fault = none := by
  obtain ⟨cta, family, rfl⟩ := mbarUpdateFamily hp hX hr hUpdate
  cases family with
  | query stage =>
    fin_cases stage
    · exact Query.queryStageZeroHistoryClean hp hX hr
    · exact Query.queryStageOneHistoryClean hp hX hr
  | queryReturn stage => exact Query.queryEmptyHistoryClean hp hX stage hr
  | cacheReady slot => exact (LoaderReady.readyHistoryClean hp hX (cta*l.block) slot hr).1
  | cacheEmpty slot => exact LoaderReady.emptyHistoryClean hp hX (cta*l.block) slot hr
  | scoreReady stage => exact Scores.scoreReadyHistoryNoFault hp hX stage hr
  | probability stage packet =>
    fin_cases packet
    · exact Scores.jointProbabilityHistoryNoFaultOfCuQ hp hX hCuQ stage hr
    · exact Scores.tailProbabilityHistoryNoFault hp hX stage hr
  | outputCompletion stage => exact Output.outputCompletionHistoryClean hp hX stage hr
  | statisticsCredit stage =>
    have hUsedK := usedKProtected hp hX
    have hBound := Statistics.countedExitCreditBound hp hX hCuQ hUsedK
    have hDeps := Statistics.creditDependenciesOfCountedExitBound hp hX hBound
    exact Statistics.creditHistoryClean hp hX hDeps stage hr
  | outputReady stage => exact Thread.Output.outputReadyHistoryClean hp hX hr
  | outputFree stage => exact Output.outputFreeHistoryClean hp hX stage hr
  | biasReady stage => exact Bias.biasReadyHistoryClean hp hX stage hr
  | biasEmpty stage => exact Bias.biasEmptyHistoryClean hp hX stage hr

end PTX.Kernels.TmlFa4Fwd.Protocol
