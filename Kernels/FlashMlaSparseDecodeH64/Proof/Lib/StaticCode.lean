-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Clc.ClcExecution
public import Lemmas.Execution.ShapeExecution
public import Lemmas.Flow.CommitTarget
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotCommit
public import Lemmas.Flow.NotMatrix
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.StoreValid
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.WarpUniform
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The classes of `Unsafe` the decoded code excludes: CLC, matrix, cluster

Static scans of the decoded program, each evaluated once (`decide +kernel`) and used through the
library's code checks: no cancellation request (`noClcUnsafe`), no warp matrix instruction
(`noMatrixUnsafe`), no cluster collective (`noClusterFault`). The guard and poll checks are
`Lib/StaticPoll.lean`, the commit and store checks `Lib/StaticCommit.lean`; the forms are the old
tree's (`Proof/Thread/RingSpins.lean`, `Proof/Thread/RingCommitEvents.lean`,
`Proof/Safety/StaticFaults.lean`) and tml-fa4's (`Lib/StaticCode.lean`, `Lib/StoreForm.lean`),
restated on the decoded program alone. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-! ### Cancellation, matrix and cluster instructions -/

private theorem noClcCode : kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

/-- No cancellation request is issued. -/
theorem noClcIssue (hX : Consistent l kernel A m X) {i : EvId} {s : Clc.Spec}
    {targets : List Nat} (hi : X.ClcIssue i s targets) : False := by
  obtain ⟨_, he⟩ := hi
  exact no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    noClcCode he ⟨_, _, rfl⟩

/-- **ERR-CLC**: no cancellation request, so no cancellation fault. -/
theorem noClcUnsafe (hX : Consistent l kernel A m X) : ¬ ClcUnsafe l X := by
  rintro ⟨_, _, _, _, _, _, hi, _⟩
  exact noClcIssue hX hi

private theorem noMatrixCode : kernel.code.all (fun ins => !matrixOp ins.op) = true := by
  decide +kernel

/-- **ERR-WARP-MATRIX**: the kernel issues no warp-level matrix instruction. -/
theorem noMatrixUnsafe (hX : Consistent l kernel A m X) : ¬ MatrixUnsafe l A X :=
  not_matrixUnsafe_of_none l (fun _ _ h => no_matrix_of_code hX noMatrixCode h)

/-- **No event is a warp-level matrix instruction.** -/
theorem noMatrixEvent (hX : Consistent l kernel A m X) {i : EvId} {e : Event}
    (he : X.get i = some e) : isMatrix e = false :=
  no_matrix_of_code hX noMatrixCode he

private theorem noClusterCode : kernel.code.all (fun ins => !clusterOp ins.op) = true := by
  decide +kernel

theorem noClusterEvent (hX : Consistent l kernel A m X) {i : EvId} {pc : Nat} {op : ClusterOp}
    (he : X.get i = some ⟨pc, .cluster op⟩) : False :=
  no_kind_of_code hX clusterOp (fun k => ∃ op, k = .cluster op)
    (fun _ ⟨_, h⟩ => by cases h)
    (fun hf ⟨_, hk⟩ => by simp [fires_cluster_op hf hk, clusterOp])
    noClusterCode he ⟨op, rfl⟩

/-- **ERR-CLUSTER-BARRIER**: an exit record cannot fail, and no cluster collective is issued. -/
theorem noClusterFault (hX : Consistent l kernel A m X) : ¬ ClusterFault l X := by
  rintro ⟨c, _, s, _, record, err, hsrc, _, hperform, herr⟩
  cases record with
  | exit =>
    simp only [ClusterBarrier.Record.perform, ClusterBarrier.perform] at hperform
    split at hperform
    · cases hperform
      cases herr
    · cases hperform
  | arrival cta warp release lanes =>
    cases lanes with
    | nil =>
      simp only [ClusterBarrier.Record.perform, List.map_nil, List.any_nil, Bool.false_eq_true,
        ↓reduceIte, ClusterBarrier.performAll] at hperform
      split at hperform <;> cases hperform
      cases herr
    | cons pair rest =>
      obtain ⟨_, _, pc, aligned, he⟩ := hsrc pair (by simp)
      exact noClusterEvent hX he
  | wait cta warp lanes =>
    cases lanes with
    | nil =>
      simp only [ClusterBarrier.Record.perform, List.map_nil,
        ClusterBarrier.performAll] at hperform
      split at hperform <;> cases hperform
      cases herr
    | cons pair rest =>
      obtain ⟨_, _, pc, aligned, he⟩ := hsrc pair (by simp)
      exact noClusterEvent hX he

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
