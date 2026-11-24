-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
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
public import Lemmas.Flow.Determinism
public import Lemmas.Register.RegisterFrame
public import Lemmas.Flow.Scalars
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Regs
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Flow.WarpScan
public import Lemmas.Flow.TauFrame
public import Lemmas.Step.Released
public import Lemmas.Step.ProtectedReadProgress
public import Kernels.TmlFa4Fwd.Flow.Code.Part047
public import Lemmas.Arith.WarpPrefix
public import Lemmas.Flow.Bits
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.TcTmpl
public import Lemmas.TensorStore.TensorStoreThread
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Lemmas.Step.WarpVote
public import Kernels.TmlFa4Fwd.Flow.Code.Part044
public import Kernels.TmlFa4Fwd.Flow.Code.Part045
public import Lemmas.Flow.Local
public import Kernels.TmlFa4Fwd.Assumptions.Transparency
public import Lemmas.Step.WarpShfl
public import Lemmas.Flow.WriteSpace
public import Lemmas.Snoc.ControlEffect
public import Lemmas.Flow.BulkCount
public import Mathlib.Data.List.NodupEquivFin
public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
public import Kernels.TmlFa4Fwd.Proof.SchedulerCoordinates
public import Kernels.TmlFa4Fwd.Proof.SchedulerCursor
public import Kernels.TmlFa4Fwd.Proof.SchedulerCuts
public import Kernels.TmlFa4Fwd.Proof.SchedulerDrainWords
public import Kernels.TmlFa4Fwd.Proof.SchedulerFrame
public import Kernels.TmlFa4Fwd.Proof.SchedulerGroupPrefix
public import Kernels.TmlFa4Fwd.Proof.SchedulerProtection
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanGuard
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionObservations
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionPath
public import Kernels.TmlFa4Fwd.Proof.SchedulerSelectionReads
public import Kernels.TmlFa4Fwd.Proof.SchedulerStartWord
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Proof Correction Epilogue

noncomputable section

/-- The issuing lane passed the successful acquire of this output stage. -/
def ReadyAcquire (l : Launch) (X : Execution) (i : EvId) (stage : Fin 2) : Prop :=
  ∃ wait < i.2, X.get (i.1, wait) =
    some ⟨pollPc stage, .wait (readyLoc l i.1 stage) 0 true true .cta⟩

/-- The correction lane that normalizes a logical row of the output staging box. -/
def sourceLane (l : Launch) (i : EvId) (row : Nat) : Nat :=
  (i.1 / l.block) * l.block + 256 + row

/-- The correction lane uses the same row coordinate as the tensor source slot. -/
theorem sourceLane_row {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (i : EvId) {row : Nat} (hy : row < 128) : rowOf l (sourceLane l i row) = row := by
  unfold sourceLane rowOf
  simp only [hp.block]
  omega

variable {p : Params}

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
