-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

/-! # A completed execution exists

`Correct` speaks about every consistent execution; that there is one, and one that completes
with the specified result, follows from it once the assumptions' execution constraints hold of
the empty execution (it has no election and no read). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The assumptions' execution constraints hold of the empty execution, which has no event. -/
theorem assumptions_wf : ∀ a ∈ Assumptions.all, a.wf L mem0 Execution.empty := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | trivial
    | (intro e pc x y h; simp [Execution.Elect, Execution.get, Execution.empty] at h)

/-- The model admits a completed execution on every launch for which the kernel is correct. -/
theorem completed_execution_of_correct (hpre : Pre P L mem0)
    (hc : Correct kernel Assumptions.all L mem0 (Post P mem0)) :
    ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  hc.complete_exists hpre.launchValid assumptions_wf

/-- A completed execution with the specified result exists. -/
theorem realizable_result_of_correct (hpre : Pre P L mem0)
    (hc : Correct kernel Assumptions.all L mem0 (Post P mem0)) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  hc.output_exists hpre.launchValid assumptions_wf

end PTX.Kernels.FlashKdaFwd.Proof.Top
