-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Facts
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.TaskBound
public import Kernels.Fp16Gemm8192.Proof.Bound.Work
public import Lemmas.Kernel.Correct
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # `BoundGoal`

A thread's counted events are at most `2002 + resetBudget` per successful poll of its CTA's
response barrier (`Bound.counted_work`), and it polls that barrier successfully at most once per
request of its cluster, at most `513` times (`ClcRing.polls_le`, from the thread facts and the CLC
responses `readerValues`). The asynchronous stages and the records each counted event creates are
bounded by the counted events (`terminates_of_count`; the kernel issues no linear copy, so no copy
exceeds its size bound), so every consistent execution has bounded size. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow
noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **Every thread's counted events are bounded**, uniformly over consistent executions. -/
theorem counted_le {X : Execution} (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g : Nat} (hg : g < L.threads) :
    (X.tr g).countP Event.counts ≤ 2002 + Bound.resetBudget * 513 := by
  have ht := threadFacts hpre hX
  have hv := ClcRing.readerValues hpre hX ht (Region.responseWriters hpre hX ht)
  have hw := Bound.counted_work hX ht hg
  have hp := ClcRing.polls_le hpre hX ht hv g
  exact hw.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) _)

/-- **`BoundGoal`**: consistent executions have bounded size. -/
theorem bound_goal (hpre : Pre P L mem0) : BoundGoal kernel Prod L mem0 :=
  terminates_of_count (2002 + Bound.resetBudget * 513) (fun _ hX _ hg => counted_le hpre hX hg)
    fun _ hX _ _ hc => (Safety.no_copy hX (threadFacts hpre hX) hc).elim

end
end PTX.Kernels.Fp16Gemm8192.Proof
