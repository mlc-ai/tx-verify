-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Thread.Facts
public import Kernels.AddOne.Proof.Progress
public import Kernels.AddOne.Proof.Bound
public import Kernels.AddOne.Proof.Result

@[expose] public section

/-! # The kernel's correctness

The four conclusions, each from the launch's precondition and the thread facts of every
consistent execution (`threadFacts`): no consistent execution is unsafe (`safe_goal`), every
maximal execution is complete (`progress_goal`), consistent executions have bounded size
(`bound_goal`), and a complete execution leaves the specified output (`result_goal`). Together
they are `Correct` (`PTX.correct_of`). -/

namespace PTX.Kernels.AddOne.Proof
open PTX

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0} (hpre : Pre L A x mem0) :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, fun n h => ?_,
    fun n h => ?_, fun name p v h => ?_⟩
  all_goals first
    | (have hk : kernel.maxThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.reqThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.ptrParams = [] := rfl; rw [hk] at h; cases h)

/-- **The kernel is correct** on every launch that satisfies its precondition. -/
theorem correct {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0}
    (hpre : Pre L A x mem0) : Correct kernel [] L mem0 (Post L A x mem0) :=
  have hT := fun _ hX => threadFacts hpre hX
  correct_of (safe_goal hpre hT) (progress_goal hpre hT) (bound_goal hpre hT) (result_goal hpre hT)

end PTX.Kernels.AddOne.Proof
