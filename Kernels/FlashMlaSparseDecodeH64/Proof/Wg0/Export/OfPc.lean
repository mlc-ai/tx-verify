-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime

@[expose] public section

/-! # An event at a pc of warpgroup 0's code is a lane of warpgroup 0's

A trace event at a pc in `[103, 1842)` is fired by a thread of warps 0 to 3 (`wg0_at`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The lane of an event at a pc of warpgroup 0's code is in warps 0 to 3.** -/
theorem wg0_warp_of_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hr : 103 ≤ e.pc ∧ e.pc < 1842) : MbarRow.warp L g < 4 := by
  obtain ⟨-, -, -, hw⟩ := wg0_at hp hX hFw he (noUb_kind hnu he) hr
  exact hw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
