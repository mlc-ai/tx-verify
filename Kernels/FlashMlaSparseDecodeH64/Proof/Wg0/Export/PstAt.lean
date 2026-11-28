-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PstSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # A peer store writes sixteen bytes at its place

A write event of a lane of warpgroup 0 at pc `403 + 10 k` is the lane's peer store `k`: it writes
16 bytes at `4096 (w ^^^ 2) + 16 l + 512 k` of `pExchange` (`Wg0.pst_loc`, here for any event of
the pc). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An event at pc `403 + 10 k` is a peer store at its place**: a write of the 16 bytes of the
quadrant of the lane's partner warp. -/
theorem wg0_pstAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k k0 : Nat} {e : Event}
    (hw : MbarRow.warp L g < 4) (hk0 : k0 < 8) (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc = 403 + 10 * k0) :
    ∃ a bs, e.kind = .wr a bs ∧ MemRow.WsAcc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 ^^^ 2) + 16 * (tidOf L g % 32) + 512 * k0) 16 a := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc' (by omega)
  have hs : d.site = .pst ⟨k0, hk0⟩ := site_pc_pst hk0 (by rw [← hpc]; exact hpc'.symm)
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw
  have hE2 := hE.2
  unfold Wg0.EvK at hE2
  rw [hs] at hE2
  rcases hE2 with ⟨a, bs, hk, hl, hz⟩ | ⟨f, hf⟩
  · refine ⟨a, bs, hk, ?_, hz⟩
    rw [hl, Wg0.pst_loc hp ht ⟨k0, hk0⟩]
    simp only [Loc.at, wsLoc, Loc.mk.injEq, true_and]
    omega
  · exact absurd hf (hub f)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
