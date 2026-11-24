-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Safety
public import Lemmas.Kernel.Descent

@[expose] public section

/-! # `ProgressGoal`

The kernel has no asynchronous, shuffle or barrier instruction, and a thread's first event is its
load: every pending thread of a maximal execution extends it (`Descent.progress_of_plain`), so
every maximal execution is complete. -/

namespace PTX.Kernels.AddOne.Proof
open PTX

noncomputable section

variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0}

/-- The kernel has no shuffle instruction. -/
theorem noShfl : kernel.NoShfl := rfl

/-- The kernel has no atomic read-modify-write instruction. -/
theorem noAtomic : kernel.NoAtomic := rfl

/-- A thread's first site is no barrier. -/
theorem init_not_bar {g : Nat} {ins : Instr}
    (hc : kernel.code[(code L A g).pc (code L A g).init]? = some ins) :
    ins.op.isBar = false := by
  simp only [code, Site.pc] at hc
  rw [Flow.code_load_0] at hc
  cases hc
  rfl

/-- **Every maximal execution is complete.** -/
theorem progress_goal (hpre : Pre L A x mem0)
    (hT : ∀ X, Consistent L kernel [] mem0 X → ThreadFacts L A X)
    (hsafe : SafeGoal kernel [] L mem0) : ProgressGoal kernel [] L mem0 :=
  Descent.progress_of_plain noTma noShfl noAtomic (fun _ hg => sound hpre hg) hsafe
    (fun X hX => (hT X hX).tracked) (fun X hX => no_bar (hT X hX))
    (fun _ _ _ hc => init_not_bar hc) (by simp [Execution.ExtWf])

end

end PTX.Kernels.AddOne.Proof
