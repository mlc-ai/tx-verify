-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Step.Released
public import Lemmas.Step.ProtectedReadProgress
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Step.WarpShfl
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerDrainWords
public import Kernels.TmlFa4Fwd.Proof.SchedulerProtection
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof Epilogue

noncomputable section

/-- The optional CuQ lookup in a subsequent output-drain request group. -/
@[no_expose] def OutputLaterDrainCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨3043, .rd a bytes⟩

theorem OutputLaterDrainCuQRead.get_eq {X : Execution} {i : EvId} {a : Acc}
    {bytes : List (Option Byte)} (h : OutputLaterDrainCuQRead X i a bytes) :
    X.get i = some ⟨3043, .rd a bytes⟩ := h

end
end PTX.Kernels.TmlFa4Fwd.Thread
