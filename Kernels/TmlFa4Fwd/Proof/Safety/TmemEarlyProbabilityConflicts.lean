-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemRecurringScoreConflicts
public import Kernels.TmlFa4Fwd.Proof.Protocol.EarlyProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof PTX.TcMma Thread Protocol.Scores

/-- The last quarter of a probability visit uses the elected tail packet credit. -/
def TailProbabilityStoreReuseOrder (l : Launch) (X : Execution) : Prop :=
  ∀ (stage : Fin 2) {mma store wait : EvId} {cell : Cell},
    StoreCell l X store cell → TensorStoreFootprint l store cell (.probability stage) →
    TailProbabilityStore X store → probabilityColumn stage+48 ≤ cell.column →
    MmaAccumulatorOn X mma cell (.probability stage) →
    (seen : ProbabilityStoreScore l X store stage) → seen.commit.2 ≤ mma.2 →
    MmaProbabilityAcquire l X mma stage 1 wait → StoreDoneBefore l X store mma

/-- All three early quarters use a completed joint publication. Only the last
quarter needs the separately elected softmax credit. -/
theorem ProbabilityStoreReuseOrder.ofTailPacket {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hJoint : CorrectionJointGuards l X) (hTail : TailProbabilityStoreReuseOrder l X) :
    ProbabilityStoreReuseOrder l X := by
  intro stage mma store cell hStore hFoot hOverlap seen hLater hGuards
  rcases probabilityStorePacketOfCell hp hX hStore hFoot with ⟨hEarly,_⟩ | ⟨hLast,hColumn⟩
  · obtain ⟨wait,hWait⟩ := hGuards 0
    obtain ⟨d,op,acc,mask,hMma,hSame⟩ := probabilityOverlapIssuer hp hX hStore hFoot hOverlap
    exact earlyProbabilityStoreBeforeLaterQk hp hX hJoint stage hEarly hFoot hMma
      hSame seen hLater hWait
  · obtain ⟨wait,hWait⟩ := hGuards 1
    exact hTail stage hStore hFoot hLast hColumn hOverlap seen hLater hWait

end PTX.Kernels.TmlFa4Fwd.Safety
