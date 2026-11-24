-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityOperandSources
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Lemmas.Tcgen05.TmemLatestSource
import Lemmas.Tcgen05.TcMmaResultLayout
public import Core.Tc.TcMmaSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.TcMma Thread Thread.Scores Protocol.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

/-- Every actual Tensor Memory A operand has a stable source in the live allocation. -/
theorem mmaProbabilityReadSource {i : EvId} {cell : Cell} (hRead : X.MmaACell i cell) :
    ∃ source, ReadSource l X .a source i cell := by
  have hWrites := tensorWritesSafeOfCuQ hp hX hCuQ
  have hReads := (readsSafe_iff.mp (tensorReadsSafeOfCuQ hp hX hCuQ)).2.1
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  obtain ⟨store,hStore,hBefore⟩ := probabilityStoreCandidateOfARead hp hX
    (correctionJointGuardsOfCuQ hp hX hCuQ) hRead
  obtain ⟨_,hLifetime⟩ := mmaAccessLifetime hp hX hCuQ (.inr (.inr hRead))
  apply readSourceOfCandidate hX hGuard hWrites (candidate := store) _ _
    (.inr (.inl hStore)) (.inr (.inl hBefore))
  · intro other hOther
    rcases hReads _ _ _ hRead hOther with h | h | h
    · exact .inr (.inl h.symm)
    · exact .inl h
    · exact .inr h
  · intro _ _ _ cta r hr hCover release hRelease
    exact .inl (hLifetime cta r hr hCover release hRelease)

/-- If the A operand's source is an MMA, its result is completed before the PV issue. -/
theorem mmaProbabilityMmaSourceDone {i source : EvId} {cell : Cell} (hRead : X.MmaACell i cell)
    (hSource : ReadSource l X .a source i cell) (hWrite : X.MmaCell source cell) :
    X.async.mmaDone source = true := by
  have hLane := (mmaAAndDLane hp hX hRead hWrite).symm
  have hIssue := hRead
  obtain ⟨_,_,_,_,_,_,hMma,_⟩ := hIssue
  have hGuard := guardedOfTmaSafe hX (noTmaUnsafe hp hX hCuQ)
  have hEarlier := tcStep_same_thread (tcStep_acyclic hX hGuard) hSource.2.2.1.tcStep
    hLane (mmaIsNotOrdinaryAccess hMma)
  obtain ⟨stage,hProb,hLo,hHi⟩ := mmaAProbabilityTile hp hX hRead
  have hScore : MmaAccumulatorOn X source cell (.probability stage) := by
    obtain ⟨_,_,_,_,_,_,hWriteIssue,hResult⟩ := hWrite
    exact mmaAccumulatorOnTile hp hX (tile := .probability stage)
      ⟨hLo,hHi⟩ hWriteIssue (writeCell_resultCell hResult)
  have hDone := scoreDoneBeforeProbabilityOperand hp hX
    (correctionJointGuardsOfCuQ hp hX hCuQ) stage hWrite hScore hProb hEarlier
  exact hDone.done hX.tcCommit

/-- An actual A read has a source and its value once completed MMA results are available. -/
theorem mmaProbabilityReadValue (hValues : ∀ i, CompletedValues l Assumptions.all X i) {i : EvId}
    {cell : Cell} (hRead : X.MmaACell i cell) :
    ∃ source value, ReadSource l X .a source i cell ∧
      Wrote l Assumptions.all X source cell value := by
  obtain ⟨source,hSource⟩ := mmaProbabilityReadSource hp hX hCuQ hRead
  rcases hSource.2.1 with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
  · obtain ⟨v,hValue⟩ := hValues source
      (mmaProbabilityMmaSourceDone hp hX hCuQ hRead hSource hMma) cell hMma
    exact ⟨source,v,hSource,.inl hValue⟩
  · obtain ⟨addr,vals,shape,j,hWrite,hJ,hCell⟩ := hStore
    exact ⟨source,vals[j],hSource,.inr (.inl
      ⟨addr,vals,shape,j,hWrite,List.getElem?_eq_some_iff.mpr ⟨hJ,rfl⟩,hCell⟩)⟩
  · exact (noTensorCopyOperandIssue hX hCopy).elim
  · exact (noTensorShiftIssue hX hShift).elim

end PTX.Kernels.TmlFa4Fwd.Safety
