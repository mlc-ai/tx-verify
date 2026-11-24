-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.Descent
public import Lemmas.Kernel.Goals
import Kernels.FlashMlaSparseDecodeH64.Proof.Bound.Goal
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.PendingDescent
import Kernels.FlashMlaSparseDecodeH64.Proof.Progress.TcDrain
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualPost
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tracked
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TrackingSoftmaxSuccessor
import Lemmas.Kernel.Existence

public section

/-! # Correctness from trace tracking and closing arrivals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Trace tracking and arrival at the closing barrier of maximal executions suffice for all
four correctness obligations. -/
theorem correct_of_tracking_and_closing (hpre : Pre P L mem0)
    (htrack : ∀ X, Consistent L kernel Assumptions.all mem0 X → Frame.Tracked (Machine.code P L) X)
    (hclosing : ∀ X, Maximal L kernel Assumptions.all mem0 X → Progress.AllClosingArrived L X) :
    Correct kernel Assumptions.all L mem0 (Post P mem0) := by
  have hs : GlobalWrites.SoundThreads P L := fun _ hg => Machine.code_sound hpre hg
  have hsafe : ∀ X, Consistent L kernel Assumptions.all mem0 X →
      ¬ Unsafe L kernel Assumptions.all mem0 X :=
    fun X hX => Safety.no_unsafe_of_tracked hpre hX hs (htrack X hX)
  exact correct_of ⟨kernel_groupUniform, hsafe⟩
    (fun _ X hX => Progress.complete_of_all_closing_arrivals hpre hX hs (htrack X hX.1)
      hsafe (hclosing X hX))
    (Bound.bound_of_tracked hpre hs htrack)
    (fun X _ hX hComplete hm => Result.post_of_complete hpre hs hX (htrack X hX) hComplete hm)

/-- Tracking all consistent executions suffices for correctness, including maximal progress. -/
theorem correct_of_tracking (hpre : Pre P L mem0)
    (htrack : ∀ X, Consistent L kernel Assumptions.all mem0 X → Frame.Tracked (Machine.code P L) X)
    :
    Correct kernel Assumptions.all L mem0 (Post P mem0) := by
  have hs : GlobalWrites.SoundThreads P L := fun _ hg => Machine.code_sound hpre hg
  exact correct_of_tracking_and_closing hpre htrack
    (fun _ hmax => Progress.all_closing_arrived_of_tracking hpre hmax hs htrack)

/-- Safety, progress, bounded execution, and the specified result for the frozen kernel. -/
theorem correct (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of_tracking hpre (fun _ hX =>
    MachineTracking.tracked hpre hX (fun _ hg => Machine.code_sound hpre hg))

private theorem assumptions_wf {L : Launch} {mem0 : Mem0} :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Execution.empty := by
  open Assumptions in
  simp [all, idealArith, approx, mulBf16x2, cvtBf16x2, cvtUe8m0, lg2Exact, ncReadOnly,
    paramPointers, storeDrain, sharedBits, commitOrder, Assumption.idealReal,
    Assumption.approxExact, Assumption.ncReadOnly, Assumption.commitOrderAt,
    Assumption.commitPerformedAt,
    TensorStore.ReadsDrainedBeforeExit, Execution.get, Execution.empty]

/-- The launch and assumptions admit a completed execution. -/
theorem completed_execution (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists hpre.launchValid assumptions_wf

/-- The specified result is realized by a completed execution. -/
theorem realizable_result (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  (correct hpre).output_exists hpre.launchValid assumptions_wf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
