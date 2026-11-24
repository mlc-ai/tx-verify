-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemFinalLoadSources
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputRescaleReuseOrder
import Kernels.TmlFa4Fwd.Proof.Safety.TmemCompletion
import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemOutputRescaleGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalProbabilityAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.Safety.TmemWordSizes
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof PTX.TcMma Thread Thread.Scores Protocol.Scores
open Thread.Correction (FinalizationLoadCell lastPvDominatesOutputMma lastPvAfterScoreCommit)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
include hp hX hCuQ

/-- The terminal PV fragment is the stable source of every observed finalization load cell.
Its output handshake applies in any consistent prefix, including an unfinished execution. -/
theorem finalizationLoadSourceWithTerminalPv {load : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : FinalizationLoadCell l X load cell stage) :
    ∃ source d op accum mask,
      PvInstruction X source (firstPvBlock false stage) 7 d op accum mask ∧
      X.MmaCell source cell ∧ ReadSource l X .ld source load cell ∧
      X.async.mmaDone source = true := by
  obtain ⟨hCellOwner,hLo,hHi⟩ := hLoad.geometry hp hX
  obtain ⟨source,d,op,acc,mask,hPv,hSource,hDone⟩ := hLoad.lastPv hp hX
  refine ⟨source,d,op,acc,mask,hPv,hSource,
    ⟨hLoad.neMma hSource,.inl hSource,.inl (.inl hDone),?_,?_⟩,
    hDone.done hX.tcCommit⟩
  · intro other hOther
    rcases hOther with hMma | hStore | ⟨_,_,_,_,hCopy,_⟩ | ⟨_,hShift,_⟩
    · rcases lastPvDominatesOutputMma hp hX stage hPv hSource hMma ⟨hLo,hHi⟩ with h | h
      · exact .inl h
      · exact .inr (.inl (.inl (.inr h)))
    · obtain ⟨tile,hFoot⟩ := tensorStoreFootprint hp hX hStore
      have hTile : tile = .rescale stage := by
        have hStoreLo := hFoot.columnLo
        have hStoreHi := hFoot.columnHi
        cases tile with
        | probability k =>
          have hRange := probabilityColumn_range k
          have hScore := scoreColumn_range k
          simp only [TensorStoreTile.columns] at hStoreHi
          unfold outputColumn at hLo
          omega
        | rescale k =>
          simp only [TensorStoreTile.columns,outputColumn] at hLo hHi hStoreLo hStoreHi
          have hSame : k = stage := Fin.ext (by omega)
          rw [hSame]
      subst tile
      have hRescale := outputRescaleStoreOfCell hp hX hStore hFoot
      obtain ⟨seen⟩ := rescaleStatisticsObservedScore hp hX hCuQ hRescale
      have hOwner := (mmaWrittenCellCta hp hX hSource).symm.trans hFoot.cta
      have hEarlier := lastPvAfterScoreCommit hp hX stage hPv (hOwner.symm ▸ seen.score)
      obtain ⟨wait,hWait⟩ := hPv.tailJointProbabilityAcquire hp hX stage
      obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
      have hSame : SameCta l source.1 other.1 :=
        ⟨event_thread_lt hX hPv.decoded,event_thread_lt hX he,hOwner⟩
      exact .inr (.inl (.inr (.inl
        (outputRescaleBeforeGuardedMma hp hX (correctionJointGuardsOfCuQ hp hX hCuQ)
          stage hRescale ⟨_,hPv.decoded⟩ hSame seen hEarlier.le hWait))))
    · exact (noTensorCopyOperandIssue hX hCopy).elim
    · exact (noTensorShiftIssue hX hShift).elim
  · intro c r hr hCover release hRelease
    obtain ⟨hOwner,hDealloc⟩ := allocationReleaseInOwnerCta hX hr hRelease
    obtain ⟨_,_,_,hCellCta,_,_,_⟩ := hCover
    exact .inl (tensorOperationsCompletedBeforeRelease hp hX hCuQ
      (hCellOwner.symm.trans (hCellCta.trans hOwner.symm)) hDealloc)

/-- The terminal PV fragment is the stable source of every observed finalization load cell.
Its output handshake applies in any consistent prefix, including an unfinished execution. -/
theorem finalizationLoadSource {load : EvId} {cell : Cell} {stage : Fin 2}
    (hLoad : FinalizationLoadCell l X load cell stage) :
    ∃ source, X.MmaCell source cell ∧ ReadSource l X .ld source load cell ∧
      X.async.mmaDone source = true := by
  obtain ⟨source,_,_,_,_,_,hCell,hRead,hDone⟩ :=
    finalizationLoadSourceWithTerminalPv hp hX hCuQ hLoad
  exact ⟨source,hCell,hRead,hDone⟩

/-- A completed MMA value supplies the actual ordinary-load source check. -/
theorem finalizationLoadSourceValue (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    {load : EvId} {cell : Cell} {stage : Fin 2} (hLoad : FinalizationLoadCell l X load cell stage) :
    ∃ source value, ReadSource l X .ld source load cell ∧
      Wrote l Assumptions.all X source cell value := by
  obtain ⟨source,hCell,hStable,hDone⟩ := finalizationLoadSource hp hX hCuQ hLoad
  obtain ⟨value,hResult⟩ := hValues source hDone cell hCell
  exact ⟨source,value,hStable,.inl hResult⟩

/-- Each observed output load word is the finite FP32 value of its terminal
PV cell whenever completed MMA cells have their values. -/
theorem finalizationLoadFloats (hValues : ∀ i, CompletedValues l Assumptions.all X i)
    (stage : Fin 2) (chunk : Fin 16) {load : EvId} {addr : Nat} {words : List Value}
    (he : X.get load = some ⟨Correction.finalizeLoadPc stage chunk, .tc (.ld addr words .s32x32b)⟩)
    :
    ∀ j < words.length, ∃ r : ℝ, words[j]? = some (.float .f32 r) := by
  intro j hj
  let cell := tcDataCell l load.1 .s32x32b addr j
  have h := FinalizationLoadCell.ofDecoded chunk he hj (cell := cell) rfl
  obtain ⟨source,hWrite,hRead,hDone⟩ := finalizationLoadSource hp hX hCuQ h
  obtain ⟨value,hResult⟩ := hValues source hDone cell hWrite
  obtain ⟨r,rfl⟩ := mmaResultIsF32 hp hX hResult
  have hLoad : X.TLd load addr words .s32x32b := ⟨_,he⟩
  have hCell : LoadCell l X load j cell := ⟨addr,words,.s32x32b,hLoad,hj,rfl⟩
  exact ⟨r,hX.tcRead.1.f32 hLoad hCell hRead (.inl hResult)⟩

end PTX.Kernels.TmlFa4Fwd.Safety
