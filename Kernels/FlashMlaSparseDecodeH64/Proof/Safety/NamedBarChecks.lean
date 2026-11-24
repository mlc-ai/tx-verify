-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.StaticCollectives
public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AlignedCtaExit
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NamedBarTrace
import Lemmas.CtaBarrier.CtaBarrierFault

public section

/-! # Named-barrier operands and aligned sites agree across each warp -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The CTA barrier history admits each pending arrival without a resource fault. -/
theorem no_ctaBarFault (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) : ¬ CtaBarFault L X := by
  let : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩
  refine not_ctaBarFault hX ?_
  intro e f _ _ _ _ _ _ he hf
  exact (NamedBarTrace.count_of_id (g := e.1) (i := e.2) hpre hX hs ht he).trans
    (NamedBarTrace.count_of_id (g := f.1) (i := f.2) hpre hX hs ht hf).symm

/-- Each ordinal of the warp's named-barrier trace has a single pair of operands. -/
theorem no_barMismatch (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) : ¬ BarMismatch L X := by
  rintro (⟨_, _, _, _, _, _, _, _, _, _, hw, he, hf, hOrd, hDiff⟩ | h)
  · obtain ⟨hi, hc, _⟩ := NamedBarTrace.agree hpre hX hs ht hw he hf hOrd
    exact hDiff.elim (fun h => h hi) (fun h => h hc)
  · exact no_barArriveMismatch hX h

/-- A warp agrees on aligned named-barrier sites and exits only after its launch gate. -/
theorem no_aligned_bar (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ (AlignedClass.bar.Divergent L kernel X ∨ AlignedClass.bar.Exited L kernel X) := by
  rintro (h | h)
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hw, he, hf, hOrd, ha, hDiff⟩ :=
      (AlignedClass.divergent_bar_iff L).mp h
    exact hDiff ((NamedBarTrace.agree hpre hX hs ht hw he hf hOrd).2.2 ha)
  · exact no_aligned_bar_exited hpre hX hs ht h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
