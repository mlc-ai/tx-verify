-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TmemOutputRescaleConflicts
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemProbabilityOperandOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.ScoreToProbabilityOperand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Protocol.Scores Thread

/-- On a protected CuQ prefix, each earlier QK write overlapping a PV probability
operand is complete before that PV instruction. -/
theorem earlierScoreToProbabilityReadOfCuQ {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) :
    ∀ stage, EarlierScoreToProbabilityRead l X stage := by
  intro stage reader writer cell hRead hWrite hQk hEarlier
  exact .inl (.inl (.inl (scoreDoneBeforeProbabilityOperand hp hX
    (correctionJointGuardsOfCuQ hp hX hCuQ) stage hWrite hQk hRead hEarlier)))

/-- MMA Tensor Memory operands are race-free on each consistent prefix with
protected CuQ. -/
theorem tensorReadsSafeOfCuQ {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) : ReadsSafe l X :=
  tensorReadsSafe hp hX (tensorMixedWriteOrderOfCuQ hp hX hCuQ)
    (tensorAStoreOrderOfCuQ hp hX hCuQ)
    (EarlierMmaAOrder.ofScore hp hX (earlierScoreToProbabilityReadOfCuQ hp hX hCuQ))

end PTX.Kernels.TmlFa4Fwd.Safety
