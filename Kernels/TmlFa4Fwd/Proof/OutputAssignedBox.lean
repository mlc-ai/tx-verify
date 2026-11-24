-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.ScheduleGeometry
public import Kernels.TmlFa4Fwd.Proof.SchedulerCoordinates
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
public import Kernels.TmlFa4Fwd.Proof.CuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Kernels.TmlFa4Fwd.Proof.MmaRoleCut
public import Kernels.TmlFa4Fwd.Proof.MmaRoleFrame
public import Kernels.TmlFa4Fwd.Proof.NoCancellation
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputRegionTransparency
public import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
public import Kernels.TmlFa4Fwd.Proof.PrologueScheduler
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency
public import Kernels.TmlFa4Fwd.Proof.SchedulerArith
public import Kernels.TmlFa4Fwd.Proof.SchedulerBallot
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
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerBallotProgress
public import Kernels.TmlFa4Fwd.Proof.WarpFollows
public import Kernels.TmlFa4Fwd.Proof.WarpOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof PTX.EventFrame Mma

noncomputable section

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first batch pos lane : Nat} {o : Option TState} {before t : TState}
    {F : List (Nat × Value)} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) (hl : lane < 32) (hLane : laneOf l g = lane)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) (hStartup : schedulerStartupFrame p l g ⊆ F)
include hp hFirst hGroup hBatch hLo hHi hl hLane hF hStartup

end

/-- The output box belongs to the request interval and coordinates assigned to its CTA. -/
def AssignedOutputBox (p : Params) (l : Launch) (g cta : Nat) (spec : TensorStore.Spec) : Prop :=
  ∃ batch < p.batch, ∃ (stage : Fin 2) (box : Fin 4),
    tilePrefix p batch * p.heads ≤ cta ∧ cta < tilePrefix p (batch + 1) * p.heads ∧
    spec = writebackStoreSpec p l g batch (assignedCoordinates p batch cta).2
      (assignedCoordinates p batch cta).1 stage box

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends) (hLow : tilePrefix p first * p.heads ≤ cta)
    (hHigh : cta < tilePrefix p (min p.batch (first + 31)) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
include hp hX hg cur hLow hHigh hF

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
