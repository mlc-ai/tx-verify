-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Resource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceExitTrace
import Lemmas.Clc.ClcExecution

public section

/-! # A finished CTA has released its Tensor Memory allocation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every launched warp-zero lane returns only after its CTA's deallocation has completed. -/
theorem no_releaseUnsafe (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ Tmem.Pair.ReleaseUnsafe L X := by
  rintro ⟨hexit, _, hnot⟩
  apply hnot
  apply released_of_dealloc hpre hX hs ht
  intro cta hg
  let g := cta * L.block
  rcases hexit g hg with hc | ⟨tag, he⟩
  · obtain ⟨_, _, hOwner⟩ := hc
    obtain ⟨_, _, _, _, hIssue, _⟩ := hX.clc.canceled_has_issue hOwner
    exact (GlobalWrites.no_clc hX hIssue).elim
  · rw [List.getLast?_eq_getElem?] at he
    have hEvent : X.get (g, (X.tr g).length - 1) = some ⟨tag, .exit⟩ := he
    have hw : warpOf L g = 0 := by
      simp [warpOf, tidOf_eq hpre, g, hpre.block]
    obtain ⟨j, hj, t, hd⟩ :=
      ResourceEvents.dealloc_before_exit hpre hX (hs g hg).machine ht hw hEvent rfl
    have hi := PTX.len_of_get hEvent
    change (X.tr g).length - 1 < (X.tr g).length at hi
    refine ⟨j, t, hd, ?_⟩
    change j + 1 < (X.tr g).length
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
