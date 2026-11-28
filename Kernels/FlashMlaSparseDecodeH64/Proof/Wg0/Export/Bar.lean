-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Bar

@[expose] public section

/-! # Warpgroup 0's named-barrier row

`barRow_wg0`: a barrier event of a lane of warps 0–3 at a pc of warpgroup 0's code is fired from a
warpgroup-0 state (`wg0_at`) whose site is a barrier site (`Wg0.evK_bar`): barrier 9 of 128
threads at the eight `wg0_sync` pcs, the warp pair's barrier `10 + warp % 2` of 64 threads at 475
(`Wg0.barW_warp`), barrier 12 without a count at 1835. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `BarRow.Wg0`**: a barrier event of a lane of warpgroup 0 is one of `Wg0Use`. -/
theorem barRow_wg0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Wg0 P L X := by
  intro g k e _ he hat hb
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Execution.isBar] at hb
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, -, ⟨hpc, hk⟩, -⟩ := wg0_at hp hX hFw he hub hr
  unfold BarRow.Wg0Use BarRow.wg0NineSites BarRow.Sync BarRow.Everyone
  rw [hpc, ← Wg0.barW_warp hp]
  exact Wg0.evK_bar hub hk hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
