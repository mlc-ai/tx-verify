-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.NoBarArrive
public import Kernels.RowSum.Proof.Events
public import Lemmas.Kernel.Descent

@[expose] public section

/-! # `row_sum`: progress

A kernel without barriers, asynchronous instructions and shuffles: every pending thread of a
maximal execution performs its next event. -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0}

/-- The kernel has no atomic read-modify-write instruction. -/
theorem noAtomic : kernel.NoAtomic := rfl

/-- **Every maximal execution is complete.** -/
theorem progress (hcode : CodeFacts L A B M K)
    (htf : ∀ X, Consistent L kernel Prod mem0 X → ThreadFacts L A B M K x X)
    (hsafe : SafeGoal kernel Prod L mem0) : ProgressGoal kernel Prod L mem0 :=
  Descent.progress_of_plain noTma noShfl noAtomic hcode.sound hsafe (fun X hX => (htf X hX).tracked)
    (fun X hX _ _ _ _ => no_bar (htf X hX) hX) (fun g _ => hcode.init_not_bar g)
    (by simp [Execution.ExtWf, Assumptions.idealAdd])

end
end PTX.Kernels.RowSum.Proof
