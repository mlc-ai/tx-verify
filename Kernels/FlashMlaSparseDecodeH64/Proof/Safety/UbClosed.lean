-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.UbRoles
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbMmaData
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbMmaReturn
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.UbWg0

public section

/-! # Absence of undefined instruction events in followed executions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel emits no undefined instruction events on a consistent, followed execution. -/
theorem no_ub (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) : ¬ HasUb X :=
  no_ub_of_wg0_mma hpre hX hs ht (fun _ hg => UbWg0.tmpl_ok hpre hg)
    (fun _ hg => UbMma.tmpl_ok hpre hg) (UbWg0.next_live hpre hX hs)
    (UbMma.next_live hpre hX hs)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
