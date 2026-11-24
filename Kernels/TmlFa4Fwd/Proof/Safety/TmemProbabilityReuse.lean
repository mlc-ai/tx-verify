-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemEarlyProbabilityConflicts
public import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityReuseOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Protocol.Scores

/-- Each later QK uses the completed publication of the overlapping probability cell. -/
theorem probabilityStoreReuseOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hJoint : CorrectionJointGuards l X) : ProbabilityStoreReuseOrder l X := by
  apply ProbabilityStoreReuseOrder.ofTailPacket hp hX hJoint
  intro stage mma store wait cell hStore hFoot hTail hCol hOverlap hSeen hLater hAcquire
  obtain ⟨d,op,acc,mask,hMma,hSame⟩ := probabilityOverlapIssuer hp hX hStore hFoot hOverlap
  exact tailProbabilityStoreBeforeLaterQk hp hX stage hTail hFoot hMma hSame hSeen hLater hAcquire

/-- Mixed probability/score writes are ordered for every consistent prefix.
Only the independent output rescale protocol is needed for all mixed writes. -/
theorem TensorMixedWriteOrder.ofOutputRescale {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hJoint : CorrectionJointGuards l X)
    (hRescale : ∀ stage, TensorMmaStoreOrder l X (.rescale stage)) :
    TensorMixedWriteOrder l X :=
  TensorMixedWriteOrder.ofProbabilityReuse hp hX (probabilityStoreReuseOrder hp hX hJoint) hRescale

end PTX.Kernels.TmlFa4Fwd.Safety
