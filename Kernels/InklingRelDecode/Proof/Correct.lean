-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

/-! # The public theorems

`correct_of_pre`, `completed_execution_of_pre` and `realizable_result_of_pre` are the three
theorems `Theorem.lean` uses. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX

/-- **The kernel is correct** on every launch that satisfies `Pre`. -/
theorem correct_of_pre {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0) :
    Correct kernel Assumptions.all L mem0 (Post Q mem0) :=
  Top.correct hpre

/-- The assumptions are well-formed on the empty execution, which has no event. -/
theorem assumptions_wf {L : Launch} {mem0 : Mem0} :
    ∀ a ∈ Assumptions.all, a.wf L mem0 Execution.empty := by
  intro a ha
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | trivial
    | (intro g j j' pc sp r h; simp [Execution.get, Execution.empty] at h)
    | (intro e pc a bs h; simp [Execution.get, Execution.empty] at h)

/-- The model admits a completed execution on every launch that satisfies `Pre`. -/
theorem completed_execution_of_pre {Q : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre Q L mem0) : ∃ X, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X :=
  (correct_of_pre hpre).complete_exists hpre.launchValid assumptions_wf

/-- A completed execution with the specified output exists on every launch that satisfies
`Pre`. -/
theorem realizable_result_of_pre {Q : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre Q L mem0) :
    ∃ X mf, Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post Q mem0 mf :=
  (correct_of_pre hpre).output_exists hpre.launchValid assumptions_wf

end PTX.Kernels.InklingRelDecode.Proof
