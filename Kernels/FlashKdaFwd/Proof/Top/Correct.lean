-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Top.Result
public import Lemmas.Kernel.Goals

@[expose] public section

/-! # The kernel is correct, from stated premises (top-level skeleton)

`Correct` has four parts: safety (no consistent execution has undefined behaviour or a data
race), progress (an execution that cannot be extended is complete), termination (a bound on the
number of counted events) and the result (the final memory satisfies `Post`). This file
assembles them with `correct_of` from the premises that are still to be proved, collected in
`Premises`:

* `safety`: the facts of `SafetyFacts` (`Top/Safety.lean`) for every consistent execution;
* `progress` and `bound`: the two goals themselves, taken as they are (their decomposition is
  planned separately; progress may use safety);
* `result`: the facts of `ResultFacts` (`Top/Result.lean`) for every consistent execution.

When every field of `Premises` is a theorem under `Pre`, `correct_of_premises` is the kernel's
theorem `correct`. Nothing here is assumed about the kernel beyond `Pre` and `Premises`; the
fourteen safety classes that the decoded program excludes are proved in `Top/Static.lean`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The remaining work of the proof**, for one launch: the safety facts and the result facts
of every consistent execution, progress given safety, and the termination bound. -/
structure Premises (P : Params) (L : Launch) (mem0 : Mem0) : Prop where
  /-- The kernel-specific safety facts hold of every consistent execution. -/
  safety : ∀ X, Consistent L kernel Assumptions.all mem0 X → SafetyFacts P L mem0 X
  /-- Given safety, an execution that no consistent execution extends by a counted event is
  complete: every thread has exited and every asynchronous operation has finished. -/
  progress : SafeGoal kernel Assumptions.all L mem0 → ProgressGoal kernel Assumptions.all L mem0
  /-- Some number bounds the size of every consistent execution. -/
  bound : BoundGoal kernel Assumptions.all L mem0
  /-- The kernel-specific result facts hold of every consistent execution. -/
  result : ∀ X, Consistent L kernel Assumptions.all mem0 X → ResultFacts P L mem0 X

/-- **The kernel is correct on every launch that satisfies `Pre` and the premises.** -/
theorem correct_of_premises (hp : Pre P L mem0) (H : Premises P L mem0) :
    Correct kernel Assumptions.all L mem0 (Post P mem0) :=
  correct_of (safe_of_facts hp H.safety) H.progress H.bound fun X _ hX hd hf =>
    post_of_facts (H.safety X hX) (H.result X hX) hd hf

end PTX.Kernels.FlashKdaFwd.Proof.Top
