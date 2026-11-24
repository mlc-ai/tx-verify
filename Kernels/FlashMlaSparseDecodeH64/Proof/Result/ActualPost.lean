-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.FinalOutput
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualOutputTile
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Wg0EpilogueMass

@[expose] public section

/-! # The actual completed output and LSE satisfy the sparse decode specification -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow

/-- A completed, followed execution satisfies the output, LSE and untouched-byte postcondition. -/
theorem post_of_complete {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hs : GlobalWrites.SoundThreads P L)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (ht : Frame.Tracked (Machine.code P L) X) (hComplete : Complete L X)
    {m : FinalMem} (hm : IsFinal L mem0 X m) : Post P mem0 m := by
  apply post_of_complete_payloads hpre hs hX ht hComplete hm
  · intro g i d tile reg e words hState hSite hGet hLoad
    have hMass := Wg0EpilogueMass.of_state hpre hX hs ht hGet hState (by rw [hSite]; rfl)
    exact Wg0EpilogueMass.normalize_cell hpre hMass
      (output_load_value reg hpre hX hs ht hComplete hGet hState hSite hLoad)
  · intro g i d a hState hSite hWrite k
    exact Wg0EpilogueMass.lse_bytes_of_write hpre hX hs ht hState hSite hWrite k

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
