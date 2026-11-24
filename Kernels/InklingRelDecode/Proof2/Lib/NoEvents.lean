-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.Regions
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotAsyncArrive
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotClc
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotTensorPrefetch
public import Lemmas.Flow.NotNc
public import Lemmas.Execution.NoTcCp

@[expose] public section

/-!
# Event kinds the kernel has none of

Decided on the decoded program (`decide +kernel` over its instructions): no bulk copy, no
cancellation request, no tensor store, no `mbarrier.inval`, no
`cp.async.mbarrier.arrive`; so no event of these kinds exists in a consistent
execution (`no_kind_of_code`). The same facts as the first tree's `Interface/OutputFrame.lean`,
for the second tree without its imports.
-/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

theorem kernel_noBulk : kernel.code.all (fun ins => !bulkOp ins.op) = true := by
  decide +kernel

theorem kernel_noClc : kernel.code.all (fun ins => !clcOp ins.op) = true := by
  decide +kernel

theorem kernel_noTensorStore : kernel.code.all (fun ins => !tensorStoreOp ins.op) = true := by
  decide +kernel

theorem kernel_noInval : kernel.code.all (fun ins => !invalOp ins.op) = true := by
  decide +kernel

theorem kernel_noAsyncArrive : kernel.code.all (fun ins => !asyncArriveOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no `mbarrier.inval`.** -/
theorem no_inval (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc}, X.get i ≠ some ⟨pc, .mbInval m⟩ :=
  fun he => no_kind_of_code hX invalOp (fun k => ∃ m, k = .mbInval m)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_mbInval_op hf hk)
    kernel_noInval he ⟨_, rfl⟩

/-- **The kernel has no `cp.async.mbarrier.arrive`.** -/
theorem no_asyncArrive (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {m : Loc} {n : Bool}, X.get i ≠ some ⟨pc, .asyncArrive m n⟩ :=
  fun he => no_kind_of_code hX asyncArriveOp (fun k => ∃ m n, k = .asyncArrive m n)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_asyncArrive_op hf hk)
    kernel_noAsyncArrive he ⟨_, _, rfl⟩

/-- **The kernel has no bulk copy.** -/
theorem no_copy (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec}, X.get i ≠ some ⟨pc, .copy s⟩ :=
  fun he => no_kind_of_code hX bulkOp (fun k => ∃ s, k = .copy s)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulk_op hf hk)
    kernel_noBulk he ⟨_, rfl⟩

/-- **The kernel has no cancellation request.** -/
theorem no_clc (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {s : Clc.Spec} {t : List Nat},
      X.get i ≠ some ⟨pc, .clcIssue s t⟩ :=
  fun he => no_kind_of_code hX clcOp (fun k => ∃ s t, k = .clcIssue s t)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_clcIssue_op hf hk)
    kernel_noClc he ⟨_, _, rfl⟩

/-- **The kernel has no tensor store.** -/
theorem no_tensorStore (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {s : TensorStore.Spec},
      X.get i ≠ some ⟨pc, .tensorStore a s⟩ :=
  fun he => no_kind_of_code hX tensorStoreOp (fun k => ∃ a s, k = .tensorStore a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorStore_op hf hk)
    kernel_noTensorStore he ⟨_, _, rfl⟩


theorem kernel_noBulkPrefetch : kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no bulk prefetch.** -/
theorem no_bulkPrefetch (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc}, X.get i ≠ some ⟨pc, .bulkPrefetch a⟩ :=
  fun he => no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk)
    kernel_noBulkPrefetch he ⟨_, rfl⟩

theorem kernel_noTensorPrefetch :
    kernel.code.all (fun ins => !tensorPrefetchOp ins.op) = true := by decide +kernel

/-- **The kernel has no tensor prefetch.** -/
theorem no_tensorPrefetch (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc a : Nat} {s : TensorPrefetch.Spec},
      X.get i ≠ some ⟨pc, .tensorPrefetch a s⟩ :=
  fun he => no_kind_of_code hX tensorPrefetchOp (fun k => ∃ a s, k = .tensorPrefetch a s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_tensorPrefetch_op hf hk)
    kernel_noTensorPrefetch he ⟨_, _, rfl⟩

/-- **The kernel has no non-coherent load**: no assumption of the kernel allows one at any
position (`Assumption.ncLoads`). -/
theorem no_nc (hX : Consistent L kernel Assumptions.all mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc} {bs : List (Option Byte)},
      X.get i ≠ some ⟨pc, .nc a bs⟩ := by
  intro i pc a bs he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, htpc, -, hfire⟩
  · cases hf
  · exact fires_not_nc (by rw [htpc]; rfl) hfire rfl

theorem kernel_noTcCp : kernel.NoTcCp = true := by decide +kernel

/-- **The kernel issues no `tcgen05.cp`.** -/
theorem no_cp (hX : Consistent L kernel Assumptions.all mem0 X) : ∀ i c, ¬ X.CpIssue i c :=
  noCp_of_consistent kernel_noTcCp hX
end
end PTX.Kernels.InklingRelDecode.Proof2
