-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RowSum.Proof.Thread.Facts
public import Kernels.RowSum.Proof.Safety.Goal
public import Kernels.RowSum.Proof.Progress.Goal
public import Kernels.RowSum.Proof.Bound.Goal
public import Kernels.RowSum.Proof.Result.Final

@[expose] public section

/-! # `row_sum`: the kernel's correctness

The four conclusions, each from the launch's precondition alone: no consistent execution is
unsafe, every maximal execution is complete, consistent executions have bounded size, and a
complete execution leaves the row sums. Together they are `Correct` (`PTX.correct_of`). -/

namespace PTX.Kernels.RowSum.Proof
open PTX PTX.Proof

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0}

theorem safe_goal (hpre : Pre L A B M K x mem0) : SafeGoal kernel Prod L mem0 :=
  ⟨rfl, fun _ hX => safe hpre (threadFacts hpre hX) hX⟩

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {L : Launch} {A B M K : Nat} {x : Nat → ℝ} {mem0 : Mem0} (hpre : Pre L A B M K x mem0)
    :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, fun n h => ?_,
    fun n h => ?_, fun name p v h => ?_⟩
  all_goals first
    | (have hk : kernel.maxThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.reqThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.ptrParams = [] := rfl; rw [hk] at h; cases h)

/-- **The kernel is correct** on every launch that satisfies its precondition. -/
theorem correct (hpre : Pre L A B M K x mem0) :
    Correct kernel Prod L mem0 (Post L B M K x mem0) :=
  correct_of (safe_goal hpre)
    (progress (codeFacts hpre) (fun _ hX => threadFacts hpre hX))
    (bound (codeFacts hpre) fun _ hX => threadFacts hpre hX)
    (result hpre fun _ hX => threadFacts hpre hX)

end PTX.Kernels.RowSum.Proof
