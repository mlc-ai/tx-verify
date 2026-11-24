-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Facts
public import Kernels.RmsNorm.Proof.Safety.Safe
public import Kernels.RmsNorm.Proof.Progress.Threads
public import Kernels.RmsNorm.Proof.Bound
public import Kernels.RmsNorm.Proof.Result.Final

@[expose] public section

/-! # The kernel's correctness

The four conclusions, each from the launch's precondition and the thread facts of every
consistent execution (`thread_facts`): no consistent execution is unsafe (`safe`), every maximal
execution is complete (`progress_goal`), consistent executions have bounded size (`bound_goal`),
and a complete execution leaves the specified output (`result`). Together they are `Correct`
(`PTX.correct_of`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.hyp.oneDimLaunch, fun n h => ?_, fun n h => ?_,
    fun name p v h => ?_⟩
  · have hk : kernel.maxThreads = some 256 := rfl
    rw [hk, Option.some.injEq] at h
    rw [hpre.hyp.block, ← h]
  all_goals first
    | (have hk : kernel.reqThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.ptrParams = [] := rfl; rw [hk] at h; cases h)

/-- **The kernel is correct** on every launch that satisfies its precondition. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    Correct kernel Prod L mem0 (Post P mem0) :=
  correct_of ⟨tcGroupUniform, fun _ hX => safe hpre hX (thread_facts hpre hX)⟩
    (progress_goal hpre fun _ hX => thread_facts hpre hX) (bound_goal hpre)
    (fun _ _ hX hc hfin => result hpre hX (thread_facts hpre hX) hc hfin)

end PTX.Kernels.RmsNorm.Proof
