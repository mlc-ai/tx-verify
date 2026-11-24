-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityNumeric
public import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningProbabilityOperandFinite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.TcMma PTX.AsyncCopy Thread Softmax
open PTX.Kernels.TmlFa4Fwd.Thread.Scores

/-- The observed store at a later PV input comes from one of the two repeated
paths. Its payload is obtained from the affine frame of its actual statistics write. -/
theorem laterCompletedPvProbabilitiesOfFrames {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : ∀ mode g pos a data,
      StatisticsStore X (g,pos) (rescaleStore (decide (mode = .biased))) a data →
      pos+2 < (X.tr g).length → RepeatedProbabilityAfterCoefficient p l X mode g pos)
    (hCuQ : Epilogue.DrainCuQProtected p X) :
    LaterCompletedPvProbabilitiesAreBf16 l X := by
  intro i result block step d op acc mask row col ops hPv _ hWrite hOps k hk cell hByte seen hLater
  obtain ⟨mode,hStore⟩ := laterProbabilityStoreOfCell hp hX seen.cellWritten
    seen.footprint hLater
  obtain ⟨a,s,weights,hPacked⟩ :=
    repeatedProbabilityPackedOfCoefficient hp hX mode (hFrame mode) hStore
  obtain ⟨_,_,hWord⟩ := probabilityStoreWordOfPackedVector hPacked seen.cellWritten
  obtain ⟨pCell,hCells⟩ := pvProbabilityCell hp hX hPv hWrite hk
  have hCell : pCell = cell := by
    have hFirst : aCell op (Mma.qkByteIndex row k 0) = some (pCell, 2 * (k % 2)) := by
      simpa using hCells (0 : Fin 2)
    rw [hByte] at hFirst
    exact congrArg Prod.fst (Option.some.inj hFirst).symm
  subst pCell
  exact pvProbabilityElementOfStoreWord hp hX hCuQ ⟨_,hPv.decoded⟩ hCells hOps seen hWord

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
