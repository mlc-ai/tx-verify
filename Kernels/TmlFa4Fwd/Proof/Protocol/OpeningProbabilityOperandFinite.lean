-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityOperandFinite
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityStoreValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.TcMma PTX.AsyncCopy Thread Softmax

/-- Opening publications in a consistent prefix supply actual BF16 pairs,
including on physical padding rows. -/
theorem openingProbabilityWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {store : EvId} {cell : Cell} (hFirst : OpeningProbabilityStore X store)
    (hCell : StoreCell l X store cell) :
    ∃ lo hi : ℝ, StoreValue l X store cell (.pair (.float .bf16 lo) (.float .bf16 hi)) := by
  obtain ⟨q,address,vals,shape,he⟩ := hFirst
  obtain ⟨batch,stage,weights,_,_,_,_,hValues,_⟩ :=
    openingProbabilityStoreValues hp hX hFootprint q he
  refine probabilityStoreWordOfPackedVector (address := address) (shape := shape)
    (weights := fun col => weights (32*q.val+col)) ?_ hCell
  exact ⟨_,hValues ▸ he⟩

/-- For completed PV inputs, the remaining arithmetic premise is restricted to
actual reads whose probability publication comes from a later softmax visit. -/
def LaterCompletedPvProbabilitiesAreBf16 (l : Launch) (X : Execution) : Prop :=
  ∀ i result block step d spec acc mask row col (ops : MmaOperands),
    PvInstruction X i block step d spec acc mask → X.async.mmaDone i = true →
    writeCell spec d mask row col = some result → X.async.mmaOperands i = some ops →
    ∀ k < 16, ∀ cell, aCell spec (Mma.qkByteIndex row k 0) = some (cell,2*(k%2)) →
      ∀ seen : ProbabilityCellPublication l X i cell, ¬ OpeningProbabilityStore X seen.store →
        ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x

/-- The actual first publication supplies all completed PV inputs omitted by the
remaining later-visit premise. -/
theorem probabilitiesBf16OfLaterCompletedReads {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hLater : LaterCompletedPvProbabilitiesAreBf16 l X) :
    Safety.CompletedPvProbabilitiesAreBf16 X := by
  intro ⟨g,j⟩ result block step d op acc mask row col ops hPv hDone hWrite hOps k hk
  have hCuQ := ((hFootprint X hX).metadataProtected hp).1
  obtain ⟨cell,hCell⟩ := pvProbabilityCell hp hX hPv hWrite hk
  have hIssue : X.MmaIssue (g,j) d op acc mask := ⟨_,hPv.decoded⟩
  have hRead : X.MmaACell (g,j) cell := ⟨_,_,_,_,_,_,hIssue,hCell 0⟩
  obtain ⟨seen⟩ := probabilityCellPublication hp hX (correctionJointGuardsOfCuQ hp hX hCuQ) hRead
  by_cases hOpening : OpeningProbabilityStore X seen.store
  · obtain ⟨_,_,hWord⟩ := openingProbabilityWord hp hX hFootprint hOpening seen.cellWritten
    exact pvProbabilityElementOfStoreWord hp hX hCuQ hIssue hCell hOps seen hWord
  · exact hLater (g,j) result block step d op acc mask row col ops hPv hDone hWrite hOps k hk
      cell (hCell 0) seen hOpening

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
