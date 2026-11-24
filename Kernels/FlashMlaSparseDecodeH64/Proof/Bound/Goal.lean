-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.BoundMachine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
open PTX PTX.Proof

/-- Every consistent execution has bounded size when it follows the tracked thread machines.
The instruction audit rules out ordinary linear copies. The size formula combines the
per-thread budget with the stages of tensor copies and stores. -/
theorem bound_of_tracked {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hsound : GlobalWrites.SoundThreads P L)
    (htracked : ∀ X, Consistent L kernel Assumptions.all mem0 X →
      Frame.Tracked (Machine.code P L) X) :
    BoundGoal kernel Assumptions.all L mem0 :=
  terminates_of_count (threadLimit P + 2)
    (fun X hX _ hg => counted_le hpre hX hsound (htracked X hX) hg)
    (fun _ hX _ _ hc => False.elim (GlobalWrites.no_copy hX hc))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Bound
