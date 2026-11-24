-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.CollectiveChecks
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaInstructions
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.ResourceRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Static
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.StaticCollectives
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.StaticFaults
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Tensor
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TensorLoads
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemReadConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemRelease
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Unalloc

@[expose] public section

/-! # Assembly of the instruction, allocation, and collective safety checks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- The instruction, allocator, collective, and per-assumption checks of `Unsafe` hold. -/
theorem unsafe_iff_execution_checks {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    Unsafe L kernel Assumptions.all mem0 X ↔
      HasUb X ∨ Race L X ∨ Mixed L X ∨ TmaUnsafe L mem0 X ∨
        SharedLifetimeUnsafe L kernel Assumptions.all X := by
  obtain ⟨hPoll, hCommit, hClc, _, hMatrix⟩ := static_checks hpre hX
  have hReg : ¬ SetMaxNReg.UnsafeAt Assumptions.all L X :=
    fun h => no_setMaxNRegUnsafe hpre hX hs ht h.unsafe
  simp only [Unsafe, no_unalloc hpre hX hs ht, no_barMismatch hpre hX hs ht,
    no_tmem_source_unsafe hpre hX hs ht, no_assumption_ub hpre hs hX ht,
    no_aligned_mismatch hpre hX hs ht, hClc, no_tensorUnsafe hpre hX hs ht,
    no_tensor_store_unsafe hpre hX hs ht, no_tensorAllocationUnsafe hpre hX hs ht,
    no_resourceUnsafe hpre hX hs ht, no_releaseUnsafe hpre hX hs ht, hPoll,
    no_tmem_access_unsafe hpre hX hs ht, hCommit, no_tmem_writes_unsafe hpre hX hs ht,
    no_mma_instruction_unsafe hpre hX hs ht, no_tmem_reads_unsafe hpre hX hs ht,
    hReg, no_ctaBarFault hpre hX hs ht, no_clusterFault hX,
    no_warpDivergent, hMatrix, no_mbar_uninit hpre hX hs ht, false_or, or_false]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
