-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

/-! # The theorem's three statements, from the proof tree -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- Safety, progress, bounded execution, and the specified result for the frozen kernel. -/
theorem correct (hpre : Pre P L mem0) : Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  Top.correct hpre

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
