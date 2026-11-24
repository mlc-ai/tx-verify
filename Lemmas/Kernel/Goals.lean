-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # The four conclusions of a kernel's correctness

A proof skeleton. `Correct` has four fields; a kernel's proof proves one goal for each, from the
launch's precondition: no consistent execution is unsafe (`SafeGoal`), every maximal execution is
complete (`ProgressGoal`), consistent executions have bounded size (`BoundGoal`), and a complete
execution leaves the specified output (`ResultGoal`). The progress goal may use the safety goal.
Together they are `Correct` (`correct_of`). -/

namespace PTX

variable (K : Kernel) (A : List Assumption) (L : Launch) (mem0 : Mem0)

/-- No consistent execution is unsafe. -/
abbrev SafeGoal : Prop :=
  K.TcGroupUniform ∧ ∀ X, Consistent L K A mem0 X → ¬ Unsafe L K A mem0 X

/-- Every maximal execution is complete. -/
abbrev ProgressGoal : Prop :=
  ∀ X, Maximal L K A mem0 X → Complete L X

/-- Consistent executions have bounded size. -/
abbrev BoundGoal : Prop :=
  ∃ N, ∀ X, Consistent L K A mem0 X → X.size L ≤ N

/-- A complete execution leaves an output satisfying `post`. -/
abbrev ResultGoal (post : FinalMem → Prop) : Prop :=
  ∀ X m, Consistent L K A mem0 X → Complete L X → IsFinal L mem0 X m → post m

variable {K A L mem0}

/-- The four conclusions are the kernel's correctness. -/
theorem correct_of {post : FinalMem → Prop} (hs : SafeGoal K A L mem0)
    (hp : SafeGoal K A L mem0 → ProgressGoal K A L mem0) (hb : BoundGoal K A L mem0)
    (hr : ResultGoal K A L mem0 post) : Correct K A L mem0 post :=
  ⟨fun _ => hs, fun _ => hp hs, fun _ => hb, fun _ => hr⟩

end PTX
