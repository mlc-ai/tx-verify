-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarPlace
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Bar

@[expose] public section

/-! # The event at pc 475 is the warp pair's barrier

The code's site at pc 475 is the pair barrier (`bar1`), a barrier site, so its event is a barrier
event (`evK_barSite`), and the barrier row gives its id `10 + warp % 2`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem site_bar1 (s : Wg0.Site) (h : s.pc = 475) : s = .bar1 := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The event at pc 475 is a barrier event of the warp pair's barrier.** -/
theorem wg0_bar1_of_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h : Nat} (hwh : MbarRow.warp L h < 4) {j : Nat}
    {e : Event} (he : X.get (h, j) = some e) (hub : ∀ u, e.kind ≠ .ub u) (hpc : e.pc = 475) :
    Execution.isBarId (10 + MbarRow.warp L h % 2) e = true := by
  obtain ⟨d, -, ⟨hpc', hk⟩, -⟩ := wg0_at hp hX hFw he hub (by omega)
  have hb : Execution.isBar e = true :=
    Wg0.evK_barSite (by rw [site_bar1 d.site (hpc'.symm.trans hpc)]; rfl) hub hk
  have hat : MbarRow.Wg0At L h e.pc := ⟨hwh, by omega, by omega⟩
  rcases barRow_wg0 hp hX hFw (Frame.lt_of_get hX he) he hat hb with ⟨hm, -⟩ | ⟨-, hs⟩ | ⟨h5, -⟩
  · simp only [BarRow.wg0NineSites, List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · obtain ⟨pc, kd⟩ := e
    simp only [BarRow.Sync] at hs
    simp [Execution.isBarId, hs]
  · omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
