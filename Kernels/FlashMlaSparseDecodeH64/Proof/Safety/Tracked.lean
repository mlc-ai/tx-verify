-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Checks
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarSafety
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MemoryConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbClosed

public section

/-! # Safety of the tracked execution -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- The tracked program rejects every form of undefined or unsafe execution. -/
theorem no_unsafe_of_tracked {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ Unsafe L kernel Assumptions.all mem0 X := by
  rw [unsafe_iff_execution_checks hpre hX hs ht]
  obtain ⟨hrace, hmixed⟩ := no_memory_conflicts hpre hX hs ht
  simp only [no_ub hpre hX hs ht, hrace, hmixed, no_tmaUnsafe hpre hX hs ht,
    SharedLifetime.no_sharedLifetimeUnsafe hpre hX hs ht, or_false, not_false_eq_true]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
