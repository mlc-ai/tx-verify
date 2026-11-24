-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Thread.Facts
public import Kernels.CopyLdg.Proof.Progress
public import Kernels.CopyLdg.Proof.Bound
public import Kernels.CopyLdg.Proof.Result

@[expose] public section

/-! # `copy_ldg`: the four conclusions assembled -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0}

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} (hpre : Pre L A B N x mem0)
    :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, fun n h => ?_, fun n h => ?_,
    fun name p v h => ?_⟩
  all_goals first
    | (have hk : kernel.maxThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.reqThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.ptrParams = [] := rfl; rw [hk] at h; cases h)

/-- **Correctness of `copy_ldg`** under the assumption `nc-read-only`. -/
theorem correct (hpre : Pre L A B N x mem0) :
    Correct kernel Nc L mem0 (Post L B N x mem0) :=
  let hthr : ∀ X, Consistent L kernel Nc mem0 X → ThreadFacts L A B N X :=
    fun _ hX => thread_facts hpre hX
  correct_of (safe_goal hpre hthr) (progress_goal hpre hthr) (bound_goal hpre hthr)
    (result_goal hpre hthr)

end
end PTX.Kernels.CopyLdg.Proof
