-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityConflicts
public import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.EarlyProbabilityReuse
public import Kernels.TmlFa4Fwd.Proof.Protocol.TailProbabilityReuseOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Protocol.Scores

/-- Every consumer acquires the relevant probability packet. Its observed score
notification orders readers before later stores of the same cell. -/
theorem probabilityStoreReadOrderOfCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (stage : Fin 2) :
    ProbabilityStoreReadOrder l X stage := by
  intro reader store cell hRead hStore hFoot
  obtain ⟨seen⟩ := probabilityStoreObservesScore hp hX stage hStore hFoot
  obtain ⟨d,op,acc,mask,early,hMma,hSame,hEarlyGuard⟩ :=
    probabilityAReadGuardOfStore hp hX stage 0 hRead hStore hFoot (.inl rfl)
  by_cases hEarlier : reader.2 < seen.commit.2
  · exact .inr (seen.doneBeforeEarlierMma hp hX hMma hSame hEarlier)
  have hLater := Nat.le_of_not_lt hEarlier
  rcases probabilityStorePacketOfCell hp hX hStore hFoot with ⟨hEarly,_⟩ | ⟨hTail,hColumn⟩
  · exact .inl (earlyProbabilityStoreBeforeLaterQk hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
      stage hEarly hFoot hMma hSame seen hLater hEarlyGuard)
  · obtain ⟨_,_,_,_,late,_,_,hTailGuard⟩ :=
      probabilityAReadGuardOfStore hp hX stage 1 hRead hStore hFoot (.inr hColumn)
    exact .inl (tailProbabilityStoreBeforeLaterQk hp hX stage hTail hFoot hMma hSame
      seen hLater hTailGuard)

/-- All ordinary Tensor Memory stores are ordered with actual A operand reads. -/
theorem tensorAStoreOrderOfCuQ {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : TensorAStoreOrder l X :=
  TensorAStoreOrder.ofProbability hp hX (probabilityStoreReadOrderOfCuQ hp hX hCuQ)

end PTX.Kernels.TmlFa4Fwd.Safety
