-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Objects
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers

@[expose] public section

/-! The proof tree's mbarrier families against the barrier inventory: the 23 offsets and counts
the families state are, as a multiset, exactly the offsets and counts of `Data/Barriers.mbars`
(the inventory lists them in the order of the prologue's initialization sites, the families in
the order of their offsets). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Audit
open PTX PTX.Kernels.FlashMlaSparseDecodeH64

/-- The families' offsets are the inventory's. -/
theorem families_offsets_perm :
    (mbars.map (·.offset)).Perm (Proof.MbarFam.all.map (·.off)) := by
  decide

/-- The families' (offset, count) pairs are the inventory's. -/
theorem families_inits_perm :
    (mbars.map fun m => (m.offset, m.count)).Perm
      (Proof.MbarFam.all.map fun f => (f.off, f.count)) := by
  decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Audit
