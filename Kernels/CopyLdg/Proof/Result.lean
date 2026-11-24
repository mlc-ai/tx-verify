-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Post
public import Kernels.CopyLdg.Proof.Safety
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.Memory
public import Lemmas.Execution.NoAsync

@[expose] public section

/-! # `copy_ldg`: the output

In a complete execution every thread below `N` has exited, so it has written `x g` to `B[g]`
(`written_of_exit`); the memory after the execution is `Post` (`post_of_writes`). -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}

/-- **`ResultGoal`.** -/
theorem result_goal (hpre : Pre L A B N x mem0)
    (hthr : ∀ X, Consistent L kernel Nc mem0 X → ThreadFacts L A B N X) :
    ResultGoal kernel Nc L mem0 (Post L B N x mem0) := by
  intro X m hX hc hfin
  have ht := hthr X hX
  have hn := noTma_of_consistent noTma hX
  have hexits := (hn.complete_iff L hX.clc).mp hc
  obtain ⟨co, -, hf⟩ := hfin
  exact post_of_writes hpre hX ht (fun h => by
      obtain ⟨i, rfl, hw | hrmw⟩ := Execution.NoTma.memWrites_thread (hn.emptyAsync hX) h
      · exact ⟨i, rfl, hw⟩
      · obtain ⟨old, hrmw⟩ := hrmw
        exact absurd hrmw (no_rmw hpre hX ht))
    (fun j hj hjN => written_of_exit hpre hX ht hjN (hexits j hj)) fun l => ⟨(hf l).1, (hf l).2.1⟩

end
end PTX.Kernels.CopyLdg.Proof
