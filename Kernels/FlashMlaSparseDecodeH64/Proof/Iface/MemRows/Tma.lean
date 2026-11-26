-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Tma producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma

@[expose] public section

/-! # The TMA warp: memory classification row

The TMA warp's code (pcs 2162–2331) makes the two length reads (non-coherent global reads) and,
per block, the reads of the four coordinate words of each of the 16 quadruples of its slot
(`coord0`–`coord3`, shared `b32` reads): element `j < 4` of quadruple `q < 16` of slot `s < 4` is
the 4 bytes at `221728 + 256 s + 16 q + 4 j` of the lane's CTA's workspace (`TmaRd`), in
`tmaCoord` (`tmaRd_in`), below the mbarriers (`tmaRd_below`). Its gathers are tensor issues, no
memory events (`Tma/Ev.lean`): `MemRow.Tma`, proved by `memRow_tma` (`Tma/Export/Mem.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

namespace MemRow

/-- **The TMA warp's read places**: element `j` of coordinate quadruple `q` of slot `s` of the
lane's CTA. -/
def TmaRd (L : Launch) (g : Nat) (a : Acc) : Prop :=
  ∃ s < 4, ∃ q < 16, ∃ j < 4, WsAcc L (g / L.block) (221728 + 256 * s + 16 * q + 4 * j) 4 a

/-- **A coordinate read lies in `tmaCoord`** of the lane's CTA. -/
theorem tmaRd_in {L : Launch} {g : Nat} {a : Acc} (h : TmaRd L g a) :
    SharedIn L (g / L.block) .tmaCoord a := by
  obtain ⟨s, hs, q, hq, j, hj, h⟩ := h
  exact wsAcc_in h (by simp only [Region.lo]; omega) (by simp only [Region.lo, Region.size]; omega)

/-- **No coordinate read reaches the mbarriers.** -/
theorem tmaRd_below {L : Launch} {g : Nat} {a : Acc} (h : TmaRd L g a) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  obtain ⟨hs, hc, hlo, hhi⟩ := tmaRd_in h
  refine ⟨hs, hc, by omega, ?_⟩
  simp only [Region.lo, Region.size] at hhi ⊢
  omega

end MemRow

/-- **Row `MemRow.Tma`**: a memory event of the TMA warp is a non-coherent read or a read of a
coordinate word (`TmaRd`). -/
def MemRow.Tma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → TmaAt L g e.pc →
    MemRow.MemEvent e → (∃ a bs, e.kind = .nc a bs) ∨
      ∃ a bs, e.kind = .rd a bs ∧ MemRow.TmaRd L g a

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
