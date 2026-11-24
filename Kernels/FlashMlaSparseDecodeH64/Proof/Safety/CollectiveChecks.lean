-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.NamedBarChecks
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.StaticCollectives
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TcCollectives

@[expose] public section

/-! # The aligned-collective checks of the frozen kernel -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- All five aligned-collective classes agree across their required participants. -/
theorem no_aligned_mismatch {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ AlignedMismatch L kernel X := by
  intro h
  rcases (alignedMismatch_iff L).mp h with h | h | h | h | h
  · exact no_aligned_tc hpre hX hs ht h
  · exact no_aligned_bar hpre hX hs ht h
  · exact no_aligned_cluster hX h
  · exact no_aligned_setMaxNReg hpre hX hs ht h
  · exact no_aligned_matrix hX h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
