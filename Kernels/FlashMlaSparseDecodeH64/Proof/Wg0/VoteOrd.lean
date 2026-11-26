-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.TcOrd

@[expose] public section

/-! # A loop site's vote ordinal

At a site of the loop that has both lengths the votes made are `r` (`r + 1` past the vote) of a
block `r` below the CTA's block count (`vOrd_loop`), with the ledger's counts at the site's
place. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch}

/-- The votes before a loop site that has both lengths: block `r` below the block count. -/
theorem vOrd_loop {g : Nat} {d : Wg0.Control.D} {n : Wg0.Cnt → Nat}
    (hJ : Wg0.RefCore L g d n) (hL : Wg0.LaunchOk P L g d)
    (hk : d.site.reg = Wg0.Reg.loop) (h2 : 2 ≤ d.site.lens) :
    ∃ r < blocksOf P L (g / L.block),
      Wg0.vOrd d = r + (if 38 < d.site.ord then 1 else 0) ∧
      Wg0.Counts (Wg0.objs L g) n true r d.site.idx none := by
  have hJ' := hJ
  unfold Wg0.RefCore at hJ'
  rw [hk] at hJ'
  obtain ⟨r, ⟨-, h26, hr, hbi, -⟩, hcnt⟩ := hJ'
  simp only [Wg0.Control.D.words] at hbi hr h26
  have hr1 : d.bi.toNat - 1 = r := by rw [hbi, toNat_W (by omega)]; rfl
  rw [Wg0.rounds_blocks hL h2] at hr
  exact ⟨r, hr, by simp only [Wg0.vOrd, hk, hr1], hcnt⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
