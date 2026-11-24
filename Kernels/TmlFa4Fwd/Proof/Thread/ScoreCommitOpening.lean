-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityParity
import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
public import Kernels.TmlFa4Fwd.Proof.MmaQkQuerySetupReplay

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.AsyncCopy PTX.MBarrier
open PTX.Kernels.TmlFa4Fwd.Mma

/-- An issued initial QK commit of this stage, before the recurring score sites. -/
@[no_expose] def OpeningScoreCommit (X : Execution) (i : EvId) (stage : Fin 2)
    (spec : TcCommit.Spec) : Prop :=
  X.get i = some ⟨(commitSite (qkCommitSite (initialQkBlock stage))).pc,.tc (.commit spec)⟩

theorem OpeningScoreCommit.decoded {X : Execution} {i : EvId} {stage : Fin 2}
    {spec : TcCommit.Spec} (h : OpeningScoreCommit X i stage spec) :
    X.get i = some ⟨(commitSite (qkCommitSite (initialQkBlock stage))).pc,.tc (.commit spec)⟩ :=
  h

theorem OpeningScoreCommit.of_decoded {X : Execution} {i : EvId} {stage : Fin 2}
    {spec : TcCommit.Spec}
    (h : X.get i = some ⟨(commitSite (qkCommitSite (initialQkBlock stage))).pc,
      .tc (.commit spec)⟩) : OpeningScoreCommit X i stage spec :=
  h

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
