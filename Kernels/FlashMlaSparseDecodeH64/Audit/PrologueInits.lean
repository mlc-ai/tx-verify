-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers

@[expose] public section

/-! The prologue's mbarrier initialization tables against the barrier inventory: the 23 site
offsets and counts are exactly `Data/Barriers.mbars`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit
open PTX PTX.Kernels.FlashMlaSparseDecodeH64

/-- The prologue's offsets, in site order, are the inventory's. -/
theorem prologue_initOff_eq :
    (List.ofFn Proof.initOff) = mbars.map (·.offset) := by
  decide

/-- The prologue's counts, in site order, are the inventory's. -/
theorem prologue_initCount_eq :
    (List.ofFn Proof.initCount) = mbars.map (·.count) := by
  decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
