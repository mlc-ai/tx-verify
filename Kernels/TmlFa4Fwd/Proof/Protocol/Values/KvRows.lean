-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.TileGeom
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.RowSource
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The row copies read the rows of the tile's keys (`kvRows`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The row copies read the rows of the tile's keys.** -/
theorem kvRows (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) : KvRows p L X := by
  intro c t hT u hu i hi row hrow d hd hk jc sp hC
  obtain ⟨-, b, ⟨hb, hlo, hhi⟩, rfl⟩ := tileOf_some hT
  obtain ⟨hyc, hyw, hyl⟩ := kvLane_spec (L := L) hp (c := c) (row := row) (d := d)
  obtain ⟨pc, hge⟩ := hC.get
  have hlt := blockLane_lt row d
  have hb512 := hp.block
  have hty : kvLane L c row d % L.block = 448 + blockLane row d := by
    unfold kvLane
    rw [hb512]
    omega
  have hgrp : LdWarp.grpOf L (kvLane L c row d) = row % 8 := by
    unfold LdWarp.grpOf
    rw [hty]
    unfold blockLane
    omega
  have hn : LdWarp.nBlk p L (kvLane L c row d) b = (workTile p c b).n := by
    unfold LdWarp.nBlk workTile
    rw [hyc]
  have hd2 : d / 64 < 2 := by omega
  obtain ⟨hz, hl⟩ := ld_row_src hp hX hFw hyw hge (b := b) (t := 2 * u + i) (i := row / 8)
    (j := d / 64) (key := (workTile p c b).key u row) (by rw [hyc]; exact hlo)
    (by rw [hyc]; exact hhi) (by omega) hd2 hC.cnt (by
      rw [hn, hgrp]
      simp only [Tile.key]
      have : (2 * u + i) / 2 = u := by omega
      rw [this]
      omega) hk
  refine ⟨hz, ?_⟩
  rw [hl, hyc, hty]
  have hm : (2 * u + i) % 2 = i := by omega
  have hlane : (448 + blockLane row d) % 8 = d % 64 / 8 := by unfold blockLane; omega
  rw [hm, hlane]
  have hlay : LdWarp.layOf p (i == 1) = if i = 0 then p.kLayout else p.vLayout := by
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
  rw [hlay]
  simp only [CacheLayout.loc, globalLoc, workTile, Loc.mk.injEq, true_and]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
