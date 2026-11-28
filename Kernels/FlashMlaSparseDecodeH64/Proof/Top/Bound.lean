-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Lemmas.Kernel.Goals
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bound
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Lemmas.Kernel.Correct

@[expose] public section

/-! # Bounded executions

`BoundGoal`: consistent executions have bounded size (`Bound.terminates`). The size counts every
thread's counted events and the asynchronous stages of each of them (`Execution.size`); the
library bounds the stages per event (`terminates_of_count`), given that every copy writes at
most `2 ^ 32` bytes, which holds vacuously here: the code issues no bulk copy (`noCopy`). Every
thread's counted events are bounded under the following premise (`thread_counts`,
`Common/Export/Bound.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Consistent executions have bounded size**, from the following premise. -/
theorem Bound.terminates (hp : Pre P L mem0)
    (hF : ∀ X, Consistent L kernel Assumptions.all mem0 X → Follow P L X) :
    BoundGoal kernel Assumptions.all L mem0 := by
  obtain ⟨N, hN⟩ := thread_counts hp
  exact terminates_of_count N (fun X hX g hg => hN X hX (hF X hX) g hg)
    fun _ hX _ _ hc => (noCopy hX hc).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
