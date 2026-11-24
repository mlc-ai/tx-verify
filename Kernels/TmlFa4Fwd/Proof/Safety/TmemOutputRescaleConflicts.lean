-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputRescaleReuseOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemOutputRescaleGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Protocol.Scores

/-- Each rescale observes its corresponding statistics generation, so all
overlapping steady and terminal PV writes are ordered through the joint packet. -/
theorem outputRescaleOrderOfCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (stage : Fin 2) :
    TensorMmaStoreOrder l X (.rescale stage) := by
  intro mma store cell hStore hFoot hOverlap
  obtain ⟨d,op,acc,mask,wait,hMma,hSame,hRescale,hGuard⟩ :=
    outputRescaleOverlap hp hX hStore hFoot hOverlap
  obtain ⟨observed⟩ := rescaleStatisticsObservedScore hp hX hCuQ hRescale
  by_cases hEarlier : mma.2 < observed.commit.2
  · exact .inl (observed.doneBeforeEarlierMma hp hX hMma hSame hEarlier)
  · exact .inr (outputRescaleBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
      stage hRescale hMma hSame observed (Nat.le_of_not_lt hEarlier) hGuard)

/-- The actual probability and rescale protocols resolve every mixed tensor write. -/
theorem tensorMixedWriteOrderOfCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : TensorMixedWriteOrder l X :=
  TensorMixedWriteOrder.ofOutputRescale hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
    (outputRescaleOrderOfCuQ hp hX hCuQ)

/-- Tensor Memory writes are safe on every consistent prefix with protected CuQ. -/
theorem tensorWritesSafeOfCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : WritesSafe l X :=
  tensorWritesSafe hp hX (tensorMixedWriteOrderOfCuQ hp hX hCuQ)

end PTX.Kernels.TmlFa4Fwd.Safety
