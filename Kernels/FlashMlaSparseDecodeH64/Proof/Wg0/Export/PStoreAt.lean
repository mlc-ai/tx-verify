-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem

@[expose] public section

/-! # A P store writes four bytes at its place

A write event of a lane of warpgroup 0 at pc `704 + j` is the lane's P store `(j, el)` for some
`el < 4`: it writes 4 bytes at `4096 (w / 2) + 512 (w % 2) + 16 l + 1024 j + 4 el` of `pExchange`
(`Wg0.ost_acc`, the place of `wg0_pStores`, here for any event of the pc). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A write at pc `704 + j` is a P store at its place.** -/
theorem wg0_ostAt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k j : Nat} {a : Acc} {bs : List Byte}
    (hw : warp L g < 4) (hj : j < 4) (he : X.get (g, k) = some ⟨704 + j, .wr a bs⟩) :
    ∃ el < 4, a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
      (204800 + 4096 * (tidOf L g / 32 / 2) + 512 * (tidOf L g / 32 % 2) +
        16 * (tidOf L g % 32) + 1024 * j + 4 * el) := by
  have hub : ∀ f, (⟨704 + j, .wr a bs⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc (by simp only; omega)
  have hs : d.site = .ost ⟨j, hj⟩ := Wg0.Data.site_pc_ost hj hpc.symm
  have ht : tidOf L g < 128 := MemRow.wg0_tid hw
  obtain ⟨hel, a', bs', hkind, hsz, hloc⟩ := Wg0.ost_acc hp ht hs hE.2 hub
  simp only [Kind.wr.injEq] at hkind
  obtain ⟨rfl, -⟩ := hkind
  exact ⟨d.el, hel, hsz, hloc⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
