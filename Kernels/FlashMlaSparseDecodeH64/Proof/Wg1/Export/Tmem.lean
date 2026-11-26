-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where

@[expose] public section

/-! # Warpgroup 1 fires no `tcgen05` event

`tmemRow_wg1`: no event of warpgroup 1's head or idle code (`wg1_state`) is a `tcgen05` event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Wg1`**. -/
theorem tmemRow_wg1 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Wg1 P L X := by
  intro g k e c _ he hat hk
  obtain ⟨σ, -, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun f h => by rw [hk] at h; cases h)
  obtain ⟨-, -, hr⟩ := hat
  rcases wg1_state hJ hi hev hpc hr with ⟨s, hs, hev, -⟩ | ⟨s, hne, hev, -, -⟩
  · rcases hs with rfl | rfl <;> simp_all [Wg1.Ev]
  · cases s <;> simp_all [Wg1.IEv]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
