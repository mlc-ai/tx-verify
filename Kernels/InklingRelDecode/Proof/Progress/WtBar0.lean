-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtBar0Lock

@[expose] public section

/-!
# `Bar0Facts` from `Bar.AlphaAgree`

`Bar0Facts.one` (`bar0_one`) and `Bar0Facts.lock` (`bar0_lock`) are proved; `Bar0Facts.alpha`, the
agreement of the default partition's threads on the count of each barrier-0 ordinal, is the one
field that remains (row "thread-layer gaps", `Bar0Facts.alpha`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **`Bar0Facts` of a safe execution, given the agreement on the counts of the loop's
barriers.** -/
theorem bar0Facts_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hs : ¬ Unsafe L kernel asms mem0 X) (halpha : Bar.AlphaAgree L X) : Bar0Facts L X where
  alpha := halpha
  one := fun hg h1 h2 => bar0_one hpre hX hS ht hg h1 h2
  lock := fun hy hy' hdiv hw h1 h2 => bar0_lock hpre hX hS ht hs hy hy' hdiv hw h1 h2

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
