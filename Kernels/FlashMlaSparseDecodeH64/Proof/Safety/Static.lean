-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingCommitEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSpins
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

@[expose] public section

/-! # Safety checks settled by the frozen instructions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Poll use and commit groups follow from the frozen stream. Cancellation, warp matrix events
  and linear reductions are absent. These checks
are independent of the kernel's numerical state and role tracking. -/
theorem static_checks (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) :
    ¬ PollShapeUnsafe kernel X ∧ ¬ TcCommitUnsafe L X ∧
      ¬ ClcUnsafe L X ∧ ¬ TensorStore.CopyReduceNoRule Assumptions.all X ∧
      ¬ MatrixUnsafe L Assumptions.all X := by
  refine ⟨RingSpins.no_pollShapeUnsafe hX, RingCommitEvents.no_commit_unsafe hpre hX, ?_, ?_, ?_⟩
  · rintro ⟨i, s, targets, q, _, _, hi, _, _, _, _⟩
    exact GlobalWrites.no_clc hX hi
  · exact TensorStore.not_copyReduceNoRule_of_none fun _ _ hc _ => (GlobalWrites.no_copy hX hc).elim
  · exact not_matrixUnsafe_of_none L fun _ _ he => GlobalWrites.no_matrix hX he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
