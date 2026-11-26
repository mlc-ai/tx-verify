-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Index producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index

@[expose] public section

/-! # The index warp: memory classification row

The index warp's code (pcs 2332–2586) makes the length and index reads (non-coherent global
reads) and, per block, the stores of the lane's coordinate pair (4 bytes at
`221728 + 256 s + 8 (t % 32) + 4 j` of the lane's CTA's workspace, element `j < 2`, for the
block's slot `s < 4` and the lane's thread index `t`) and of the quad's validity byte (1 byte at
`221696 + 8 s + (t % 32) / 4`): `MemRow.Index` (`IxWr`), proved by `memRow_index`
(`Index/Export/Mem.lean`). So every write lies in `tmaCoord` or `tokenValid` (`ixWr_in`) and
ends below the mbarriers (`ixWr_below`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

namespace MemRow

/-- **The index warp's write places**: lane `g`'s coordinate pair element `j` or validity byte
in slot `s` of its CTA. -/
def IxWr (L : Launch) (g : Nat) (a : Acc) : Prop :=
  (∃ s < 4, ∃ j < 2, WsAcc L (g / L.block)
    (221728 + 256 * s + 8 * ((L.tidOf g).x % 32) + 4 * j) 4 a) ∨
  ∃ s < 4, WsAcc L (g / L.block) (221696 + 8 * s + (L.tidOf g).x % 32 / 4) 1 a

/-- **An index write lies in `tmaCoord` or `tokenValid`** of the lane's CTA. -/
theorem ixWr_in {L : Launch} {g : Nat} {a : Acc} (h : IxWr L g a) :
    SharedIn L (g / L.block) .tmaCoord a ∨ SharedIn L (g / L.block) .tokenValid a := by
  rcases h with ⟨s, hs, j, hj, h⟩ | ⟨s, hs, h⟩
  · exact .inl (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))
  · exact .inr (wsAcc_in h (by simp only [Region.lo]; omega)
      (by simp only [Region.lo, Region.size]; omega))

/-- **No index write reaches the mbarriers.** -/
theorem ixWr_below {L : Launch} {g : Nat} {a : Acc} (h : IxWr L g a) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ L.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ L.sharedBase + Region.mbars.lo := by
  rcases ixWr_in h with ⟨hs, hc, hlo, hhi⟩ | ⟨hs, hc, hlo, hhi⟩ <;>
    refine ⟨hs, hc, by omega, ?_⟩ <;>
    simp only [Region.lo, Region.size] at hhi ⊢ <;> omega

end MemRow

/-- **Row `MemRow.Index`**: a memory event of the index warp is a non-coherent read, or a shared
write at the lane's pair or validity places (`IxWr`). -/
def MemRow.Index (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → IndexAt L g e.pc →
    MemRow.MemEvent e → (∃ a bs, e.kind = .nc a bs) ∨
    ∃ (a : Acc) (bs : List Byte), e.kind = .wr a bs ∧ MemRow.IxWr L g a

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
