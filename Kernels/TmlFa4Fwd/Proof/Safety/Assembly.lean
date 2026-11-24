-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.Alignment
public import Kernels.TmlFa4Fwd.Proof.Safety.Allocation
public import Kernels.TmlFa4Fwd.Proof.Safety.Mbar
public import Kernels.TmlFa4Fwd.Proof.Safety.NamedBarrierConflicts
public import Kernels.TmlFa4Fwd.Proof.Safety.OutputWriteAgreement
public import Kernels.TmlFa4Fwd.Proof.Safety.SharedLifetime
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemAccess
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemLoadProvenance
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedFaults
public import Kernels.TmlFa4Fwd.Proof.Thread.PollUniformity
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.Safety.TmemOutputRescaleConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.TmemReadConflicts
public import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleStoreValues
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.RegisterSafety
import Kernels.TmlFa4Fwd.Proof.StaticSafety
import Kernels.TmlFa4Fwd.Proof.TensorSafety
import Kernels.TmlFa4Fwd.Proof.Thread.MmaResourceOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollector
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueShape

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX

/-- Every issued MMA is well shaped. Only completed result values can fail the
instruction check. -/
theorem mmaInstructionCases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hUnsafe : TcMma.InstructionUnsafe l Assumptions.all X) :
    ∃ i dst spec accum mask, X.MmaIssue i dst spec accum mask ∧
      ¬ TcMma.CompletedValues l Assumptions.all X i := by
  classical
  by_contra hNone
  apply hUnsafe
  refine ⟨?_, fun _ _ hCopy => (Thread.noTensorCopyOperandIssue hX hCopy).elim,
    Thread.mmaCollectorsSafe hX⟩
  intro i dst spec accum mask hi
  exact ⟨Thread.actualMmaIssueShape hp hX hi,
    Classical.byContradiction fun hValue => hNone ⟨i, dst, spec, accum, mask, hi, hValue⟩⟩

/-- The remaining tensor arithmetic checks concern recorded input formats. -/
def TensorValueCase (X : Execution) : Prop :=
  ¬ CompletedMmaOperandsAreBf16 X ∨ ¬ Protocol.Statistics.RescaleStoreValuesAreF32 X

private theorem tensorValueCaseOfUnsafe {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    (hUnsafe : TcMma.SourceUnsafe l Assumptions.all X ∨
      TcMma.InstructionUnsafe l Assumptions.all X) :
    TensorValueCase X := by
  by_cases hOperands : CompletedMmaOperandsAreBf16 X
  · by_cases hRescale : Protocol.Statistics.RescaleStoreValuesAreF32 X
    · rcases hUnsafe with hSource | hInstruction
      · exact (hSource (tensorSourcesOfOperandsAndRescaleStores hp hX hCuQ hOperands hRescale)).elim
      · obtain ⟨i,_,_,_,_,_,hMiss⟩ := mmaInstructionCases hp hX hInstruction
        have hValues := mmaCompletedValuesOfOperandsAndRescaleStores hp hX hCuQ hOperands hRescale
        exact (hMiss (hValues i)).elim
    · exact .inr hRescale
  · exact .inl hOperands

/-- The decoded resource protocols discharge the object, allocation-lifetime, and static
checks. The remaining cases concern actual instruction faults, accesses, and convergence. -/
theorem unsafeCases {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputIntentFootprint p Y)
    (hAddresses : CuQReplayAddresses p X)
    (hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y)
    (hUnsafe : Unsafe l kernel Assumptions.all m X) :
    (∃ i f, Thread.DecodedFault X i f) ∨
    (∃ i a bytes loc, UnbackedMetadataRead p X i a bytes ∧
      a.Covers loc ∧ loc.space = .global ∧ m loc = none) ∨
    ClassifiedMemoryConflict p l X ∨ SoftmaxBarrierMismatch l X ∨
    ((AlignedClass.tc.Divergent l kernel X ∨ AlignedClass.tc.Exited l kernel X) ∨
      Thread.AlignedWorkBarrierMismatch l X 8) ∨
    TensorValueCase X := by
  have hOutput := hOutputs X hX
  have hCuQ := (outputIntent_iff_cuQProtected hp hX).mp hOutput
  have hTma := noTmaUnsafe hp hX hCuQ
  have hTensor := noActualTensorUnsafe hp hX
  have hStore := noTensorStoreUnsafe hX
  have hTensorAlloc := noActualTensorAllocationUnsafe hp hX
  have hResource := Thread.noAllocatorFault hp hX
  have hRelease := Thread.noAllocatorReleaseUnsafe hp hX
  have hAccess : ¬ Tmem.Pair.AccessUnsafe l X := fun h => h (tensorAccessSafe hp hX hCuQ)
  have hCtaBar := Protocol.noActualNamedBarrierFault hp hX hCuQ
  have hNotClc := noClcUnsafe hX
  have hCluster := noClusterFault hX
  have hMatrix := noMatrixUnsafe hX
  have hCommit := noTcCommitUnsafe hp hX
  have hPoll := noPollShapeUnsafe hX
  have hWarp := Thread.noWarpDivergenceOfPollAgreement hp hX
    (fun Y hY => (hOutputs Y hY).performed) hComplete
  have hRegister : ¬ SetMaxNReg.UnsafeAt Assumptions.all l X := fun h =>
    noRegisterRequestUnsafe hp hX h.unsafe
  have hAssumptionUb := noAssumptionUb (hOutput.noInputWrite hp)
  have hInit := noMbarUninit hp hX
  have hLifetime := noSharedLifetimeUnsafe hp hX hCuQ
  have hWrites : ¬ TcMma.WritesUnsafe l X := fun h => h (tensorWritesSafeOfCuQ hp hX hCuQ)
  have hReads : ¬ TcMma.ReadsUnsafe l X := fun h => h (tensorReadsSafeOfCuQ hp hX hCuQ)
  simp only [Unsafe, hLifetime, hWrites, hReads, hTma, hTensor, hStore, hTensorAlloc,
    hResource, hRelease, hAccess,
    hCtaBar, hNotClc, hCluster, hMatrix, hCommit, hPoll, hWarp, hRegister, hInit, hAssumptionUb,
    or_false, false_or] at hUnsafe
  have hRead (hBad : Unalloc m X) :
      ∃ i a bytes loc, UnbackedMetadataRead p X i a bytes ∧
        a.Covers loc ∧ loc.space = .global ∧ m loc = none := by
    rcases unallocatedReadSource hp hX hOutput hBad with hGlobal | ⟨i, spec, loc, hi, hCover, hm⟩
    · obtain ⟨i, a, bytes, loc, hRead, hCover, hSpace, hMem⟩ := hGlobal
      refine ⟨i, a, bytes, loc, ?_, hCover, hSpace, hMem⟩
      apply unbackedMetadataRead hp hX (fun Y hY => (hOutputs Y hY).performed)
        hAddresses hRead (hCover.1.symm.trans hSpace)
      rintro ⟨kind, value, hWord⟩
      obtain ⟨byte, hByte⟩ := hWord.allocated hp hCover
      rw [hMem] at hByte
      cases hByte
    · obtain ⟨byte, hByte⟩ := (pagedCopyCoveredSource hp hX hOutput.performed hi hCover).2
      rw [hm] at hByte
      cases hByte
  have hAligned (hBad : AlignedMismatch l kernel X) :=
    (alignmentCases hp hX hBad).imp_right fun hWork =>
      hWork.softmaxOfCorrectionAgreement hp hX
        (correctionStatisticsBeforeFinalOrdinal hp hX)
        (fun hWarp hOrd hi hj => correctionStatisticsRoundAgrees hp hX hi hj hWarp hOrd)
  apply hUnsafe.imp (Thread.decodedFaultOfUb hX) (Or.imp hRead ?_)
  intro hMemory
  exact (or_assoc.mpr hMemory).imp
    (fun h => classifyMemoryConflict hp hX hOutputs hAddresses (memoryConflictCases hp hX h))
    (Or.imp (classifyBarMismatch hp hX) (fun h => by
      rcases h with hSource | hAlign | hInstruction
      · exact .inr (tensorValueCaseOfUnsafe hp hX hCuQ (.inl hSource))
      · exact .inl (hAligned hAlign)
      · exact .inr (tensorValueCaseOfUnsafe hp hX hCuQ (.inr hInstruction))))


end PTX.Kernels.TmlFa4Fwd.Safety
