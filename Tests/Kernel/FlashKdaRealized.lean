-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Theorem
public import Tests.Kernel.FlashKdaPre

@[expose] public section

/-!
# The FlashKDA theorem speaks about an actual run

`Kernels/FlashKdaFwd/Theorem.lean` proves, for every launch that satisfies the precondition
`Pre`, that a completed execution with the specified final memory exists
(`realizable_result`). `Tests/Kernel/FlashKdaPre.lean` writes down one launch that satisfies
`Pre` (`OneToken`: one sequence, one head, one token, all inputs zero). Together they give a
statement with no hypothesis at all: there are a launch, a memory before it, an execution that
the model and the kernel's assumptions allow (`Consistent`), in which every thread has finished
(`Complete`), and a final memory of that execution (`IsFinal`) that satisfies the
postcondition `Post`. So neither the precondition nor the assumption list `Assumptions.all`
is contradictory.
-/

namespace PTX.Kernels.FlashKdaFwd
open PTX

/-- **A launch of the FlashKDA forward kernel that satisfies the precondition has a completed
execution with the specified result**, and such a launch exists. -/
theorem realized :
    ∃ (P : Params) (L : Launch) (mem0 : Mem0) (X : Execution) (mf : FinalMem),
      Pre P L mem0 ∧ Consistent L kernel Assumptions.all mem0 X ∧ Complete L X ∧
        IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  let ⟨X, mf, hX, hc, hf, hp⟩ := realizable_result OneToken.pre
  ⟨_, _, _, X, mf, OneToken.pre, hX, hc, hf, hp⟩

end PTX.Kernels.FlashKdaFwd
