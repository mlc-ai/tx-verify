-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.SafeFacts
public import Kernels.Fp16Gemm8192.Proof.ProgressFacts
public import Kernels.Fp16Gemm8192.Proof.BoundFacts
public import Kernels.Fp16Gemm8192.Proof.ValueFacts

@[expose] public section

/-! # The kernel's correctness

The four conclusions, each from the launch's precondition alone: no consistent execution is
unsafe (`safe_goal`), every maximal execution is complete (`progress_goal`), consistent executions
have bounded size (`bound_goal`), and a complete execution leaves the specified output
(`result_goal`). Together they are `Correct` (`PTX.correct_of`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof

/-- The launches `Pre` describes are ones the kernel's declarations admit (CORRECT-LAUNCH). -/
theorem valid {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    L.Valid kernel := by
  refine ⟨Launch.oneDimLaunch_clusterGridValid hpre.oneDimLaunch, fun n h => ?_, fun n h => ?_,
    fun name p v h => ?_⟩
  · have hk : kernel.maxThreads = some 384 := rfl
    rw [hk, Option.some.injEq] at h
    rw [hpre.block, ← h]
  all_goals first
    | (have hk : kernel.reqThreads = none := rfl; rw [hk] at h; cases h)
    | (have hk : kernel.ptrParams = [] := rfl; rw [hk] at h; cases h)

/-- **The kernel is correct** on every launch that satisfies its precondition. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    Correct kernel Prod L mem0 (Post P mem0) :=
  correct_of (safe_goal hpre) (progress_goal hpre) (bound_goal hpre) (result_goal hpre)

end PTX.Kernels.Fp16Gemm8192.Proof
