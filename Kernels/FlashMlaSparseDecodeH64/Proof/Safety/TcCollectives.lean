-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveTrace

public section

/-! # Warp alignment of Tensor Memory collectives -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Tensor Memory collectives agree at each warp ordinal, and each lane completes them before
exiting. -/
theorem no_aligned_tc (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ (AlignedClass.tc.Divergent L kernel X ∨ AlignedClass.tc.Exited L kernel X) := by
  rintro (h | h)
  · obtain ⟨_, _, _, _, _, _, _, hw, hek, hfk, he, hf, hdiff⟩ :=
      (AlignedClass.divergent_tc_iff L).mp h
    obtain ⟨hTag, hOperand⟩ := TcCollectiveTrace.agree hpre hX hs ht hw he hf hek hfk
    exact hdiff.elim (fun h => h hTag) (fun h => h hOperand)
  · obtain ⟨_, _, _, hw, he, hf⟩ := (AlignedClass.exited_tc_iff L).mp h
    exact TcCollectiveTrace.not_exited_short hpre hX hs ht hw he hf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
