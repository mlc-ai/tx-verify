-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.Assembly
public import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionInitialTensorCoverage
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTensorAlignment
public import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningProbabilityOperandFinite
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Result.ComputedSoftmaxRows
public import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Progress.IdleCtaExits
import Kernels.TmlFa4Fwd.Proof.Progress.ScheduledSingleVisitExit
import Kernels.TmlFa4Fwd.Proof.Progress.ScheduledRepeatedExit
import Kernels.TmlFa4Fwd.Proof.Progress.OutputExitFromCorrection
public import Kernels.TmlFa4Fwd.Proof.Thread.Machine
public import Kernels.TmlFa4Fwd.Proof.Result.SingleVisit
public import Kernels.TmlFa4Fwd.Proof.Termination
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Existence
import Kernels.TmlFa4Fwd.Proof.StaticSafety
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBarrierRank
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.OutputReadFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX

variable {p : Params} {l : Launch} {m : Mem0}

private theorem scheduledExitOfPre (hp : Pre p l m) {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hScheduled : g/l.block < tilePrefix p p.batch*p.heads) (hRole : Thread.roleOf l g ≠ .output) :
    Thread.Exited X g := by
  obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hScheduled
  have hPos := (Mma.trips_bounds hp hb (Epilogue.assignedCoordinates_valid hp hLo hHi).1).1
  have hFrame (Y : Execution) (hY : Consistent l kernel Assumptions.all m Y) :
      OutputFootprint p Y := (outputIntentFootprint hp hY).performed
  by_cases hOne : Mma.trips p batch (Epilogue.assignedCoordinates p batch (g/l.block)).1 = 1
  · exact Progress.scheduledSingleVisitExitsOfMaximal hp hMax hFrame hg hb hLo hHi hOne
  · exact Progress.scheduledRepeatedExitsOfMaximal hp hMax hFrame hg hb hLo hHi (by omega)
      hRole

private theorem allLanesExitOfPre (hp : Pre p l m) {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) : ∀ g < l.threads, Thread.Exited X g := by
  intro g hg
  by_cases hScheduled : g / l.block < tilePrefix p p.batch * p.heads
  · by_cases hOutput : Thread.roleOf l g = .output
    · have hCuQ := drainCuQProtected hp hMax.1
      apply Progress.outputExitsOfCorrectionExits hp hMax hg hOutput hCuQ hScheduled
      intro lane hl hRole hCta
      exact scheduledExitOfPre hp hMax hl (hCta.symm ▸ hScheduled)
        (by simp [hRole])
    · exact scheduledExitOfPre hp hMax hg hScheduled hOutput
  · have hCuQ := drainCuQProtected hp hMax.1
    exact Progress.idleCtaExitsOfAllGroups hp hMax hg hCuQ (Nat.le_of_not_gt hScheduled)

private theorem completeOfPre (hp : Pre p l m) {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) : Complete l X := by
  have hCuQ := drainCuQProtected hp hMax.1
  exact Progress.completeOfExitedRoles hp hMax hCuQ (allLanesExitOfPre hp hMax)

/-- Correctness of the frozen kernel under its precondition. -/
theorem correct_of_pre (hp : Pre p l m) : Correct kernel Assumptions.all l m (Post p m) := by
  have hFoot (Y : Execution) (hY : Consistent l kernel Assumptions.all m Y) :
      OutputIntentFootprint p Y :=
    outputIntentFootprint hp hY
  refine correct_of ⟨tcGroupUniform,?_⟩ ?_ (terminates hp) ?_
  · intro X hX hBad
    have hComplete : ∀ Y, Maximal l kernel Assumptions.all m Y → Complete l Y :=
      fun _ hMax => completeOfPre hp hMax
    have hProtected (Y : Execution) (hY : Consistent l kernel Assumptions.all m Y) :=
      drainCuQProtected hp hY
    have hAddresses : Safety.CuQReplayAddresses p X :=
      ⟨OutputWarp.fallbackAddresses hp hX,
        Thread.loaderFallbackAddressesOfMaximal hp hX hProtected hComplete,
        OutputWarp.laterDrainAddresses hp hX,
        Thread.softmaxFallbackAddressesOfMaximal hp hX hProtected hComplete,
        Thread.correctionFallbackAddressesOfMaximal hp hX hComplete⟩
    have hAligned := Thread.noAlignedSoftmaxWorkMismatchOfExits hp hX
      (fun Y hY => (hFoot Y hY).performed)
      (fun _ hMax g hg _ => allLanesExitOfPre hp hMax g hg)
    rcases Safety.unsafeCases hp hX hFoot hAddresses hComplete hBad with
      hFault | hRead | hConflict | hBar | (hTc | hWorkBar) | (hMma | hRescale)
    · obtain ⟨i, f, hFault⟩ := hFault
      obtain ⟨Y, hY, hPrefix, hLargest⟩ := bounded_largest_extension (terminates hp) hX
      have hMax : Maximal l kernel Assumptions.all m Y :=
        ⟨hY, fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
      exact hFault.contradictsExitsInExtension hY hPrefix (allLanesExitOfPre hp hMax)
    · obtain ⟨_, _, _, _, hUnbacked, _, _, _⟩ := hRead
      exact hUnbacked.impossible hp hX (hFoot X hX).performed
    · exact hConflict.impossible hp hX (hFoot X hX).performed
    · exact hAligned (Safety.softmaxBarrierMismatchIsAlignedWork hp hX hBar)
    · have hSoftmax :=
        Thread.softmaxTensorAlignmentOfFootprintAndCompletion hp hX hFoot hComplete
      obtain ⟨hCuQ,hUsedK⟩ := (hFoot X hX).performed.metadataProtected hp
      have hCorrection := Thread.correctionTensorSlotAlignment hp hX hUsedK
      exact Thread.alignedTensorOfArithmeticWarps hp hX
        (Thread.arithmeticTensorAlignmentOfCorrectionSlots hp hX hSoftmax hCorrection) hTc
    · exact hAligned hWorkBar
    · exact hMma (Safety.mmaOperandsOfProbabilities hp hX
        (hFoot X hX).performed
        (Protocol.Scores.completedPvProbabilitiesOfExecution hp hX
          (fun Y hY => (hFoot Y hY).performed)))
    · exact hRescale (Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hX
        (fun Y hY => (hFoot Y hY).performed))
  · intro _ _ hX
    exact completeOfPre hp hX
  · intro X out hX hDone hFinal
    have hFrame := (hFoot X hX).performed
    have hRepeated := Result.repeatedValuesOfComplete hp hX hDone
      (fun Y hY => (hFoot Y hY).performed)
    exact Result.postOfValues hp hX hDone hFinal
      (Result.outputValuesOfRepeatedVisits hp hX hDone hFrame hRepeated.1)
      (Protocol.Statistics.lseWriteValuesOfRepeatedVisits hp hX hDone hFrame
        hRepeated.2)

/-- The launch admits a completed execution. -/
theorem completed_execution_of_pre (hp : Pre p l m) :
    ∃ X, Consistent l kernel Assumptions.all m X ∧ Complete l X :=
  (correct_of_pre hp).complete_exists hp.launch Assumptions.empty_wf

/-- A completed execution with the specified final memory exists. -/
theorem realizable_result_of_pre (hp : Pre p l m) :
    ∃ X out, Consistent l kernel Assumptions.all m X ∧ Complete l X ∧
      IsFinal l m X out ∧ Post p m out :=
  (correct_of_pre hp).output_exists hp.launch Assumptions.empty_wf

end PTX.Kernels.TmlFa4Fwd
