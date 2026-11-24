-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Correct
public import Lemmas.Kernel.Existence
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

/-! # The theorem's three statements, from the proof tree -/

namespace PTX.Kernels.TmlFa4Fwd
open PTX

variable {p : Params} {l : Launch} {m : Mem0}

/-- Correctness of the frozen kernel under its precondition. -/
theorem correct_of_pre (hp : Pre p l m) : Correct kernel Assumptions.all l m (Post p m) :=
  Proof.Top.correct2 hp

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
