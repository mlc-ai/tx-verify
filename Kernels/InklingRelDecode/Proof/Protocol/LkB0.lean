-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LkB0
public import Kernels.InklingRelDecode.Proof.Safety.Aligned

@[expose] public section

/-!
# No thread exits before an aligned barrier of the CTA

* `barExited_not`: no thread exits before another participant's aligned barrier of the CTA. The
  aligned barriers without a count of the kernel are its `bar.sync 0` (the program has
  `barrier.sync 1` without `.aligned`), a thread's three: the two of the common start and the last.
  A participant's aligned barrier has at most two before it (`Interface.aln_before_le`), and an
  exiting thread has made three (`Interface.exit_aln`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No thread of the CTA exits before another participant's aligned barrier without a count.** -/
theorem barExited_not (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X) :
    ¬ AlignedClass.bar.Exited L kernel X := by
  rintro ⟨e, f, ev, -, he, hme, -, hshort⟩
  obtain ⟨⟨pc, hf⟩, hcount⟩ := hshort
  simp only [AlignedClass.exitMember] at hme hcount
  have h1 := aln_before_le hpre hX hS ht he hme
  have h2 := exit_aln hpre hX hS ht hf
  have hle := (List.take_sublist f.2 (X.tr f.1)).countP_le (p := kernel.isAlignedCtaBar)
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
