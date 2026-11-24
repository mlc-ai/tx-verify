-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AlignedCtaGate

public section

/-! # No thread exits short of an aligned full-CTA barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- Every exiting thread has reached the only aligned barrier requiring the whole CTA. -/
theorem no_aligned_bar_exited {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ AlignedClass.bar.Exited L kernel X := by
  intro h
  obtain ⟨⟨g, i⟩, ⟨f, j⟩, k, _, ⟨e, he, ha⟩, hCount, ⟨_, hf⟩, hShort⟩ :=
    (AlignedClass.exited_bar_iff L).mp h
  have hZero := AlignedCtaGate.ordinal_zero hpre hX hs ht he ha
  have hPos := AlignedCtaGate.before_exit hX hs ht hf
  change ((X.tr g).take i).countP kernel.isAlignedCtaBar = k at hCount
  change (X.tr f).countP kernel.isAlignedCtaBar ≤ k at hShort
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
