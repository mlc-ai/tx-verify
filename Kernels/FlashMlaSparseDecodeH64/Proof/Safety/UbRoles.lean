-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.HasUb
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource

public section

/-! # Reduction of undefined events to the softmax and MMA role obligations -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- In a followed execution only the softmax and MMA role obligations remain for `HasUb`. -/
theorem no_ub_of_wg0_mma (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hWg0 : ∀ g < L.threads, (Wg0.code P L g).TmplOk)
    (hMma : ∀ g < L.threads, (Wg1Mma.code P L g).TmplOk)
    (hWg0Next : UbRoles.SoftmaxContinues P L X) (hMmaNext : UbRoles.MmaContinues P L X) :
    ¬ HasUb X := by
  apply no_ub_of_live_steps hX hs ht (fun hg hd t ins ha hi hc f =>
    UbRoles.templates hpre hX hs hg (hWg0 _ hg) (hMma _ hg) hd ha hi hc f)
  intro g i d e he hd hUb hExit
  refine UbRoles.next_live hpre hX hs ht (no_resourceUnsafe hpre hX hs ht)
    hWg0Next hMmaNext he hd ?_
  rintro (⟨f, hf⟩ | hexit)
  · exact hUb f hf
  · exact hExit hexit

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
