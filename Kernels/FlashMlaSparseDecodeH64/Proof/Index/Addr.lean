-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Lemmas.Flow.Bits

@[expose] public section

/-! # The index warp's store address words as workspace offsets

For slot `s` of the ring and lane `t % 32` of the warp (`t = tidOf L g`), the coordinate pair's
word `pairW` plus `221728` is the workspace byte `221728 + 256 s + 8 (t % 32)` (`pair_loc`) and
the validity byte's word `byteW` plus `221696` is `221696 + 8 s + (t % 32) / 4` (`byte_loc`): the
shared base is below `2 ^ 32 - 222952` (`sharedBase_lt`), so no sum wraps. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The coordinate pair's store address.** -/
theorem pair_loc (hp : Pre P L m) (c : IxCtl) :
    smLoc L g (pairW L g c) 221728 =
      wsLoc L (g / L.block) (221728 + 256 * c.slot.val + 8 * (tidOf L g % 32)) := by
  have hS := sharedBase_lt hp
  have ht := tidOf_lt hp g
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  rcases c with ⟨l0, l1, cnt, neg, ⟨s, hs⟩, par, xb, xn, wpos, aptr, xa⟩
  simp only [pairW, ixRowB, ixLane, ixSlotW, tw, sbw, add32, shl, andi, r32, i32, truncBits]
  interval_cases s <;> nf_simp <;> omega

/-- **The validity byte's store address.** -/
theorem byte_loc (hp : Pre P L m) (c : IxCtl) :
    smLoc L g (byteW L g c) 221696 =
      wsLoc L (g / L.block) (221696 + 8 * c.slot.val + tidOf L g % 32 / 4) := by
  have hS := sharedBase_lt hp
  have ht := tidOf_lt hp g
  simp only [smLoc, wsLoc, Loc.mk.injEq, true_and]
  rcases c with ⟨l0, l1, cnt, neg, ⟨s, hs⟩, par, xb, xn, wpos, aptr, xa⟩
  simp only [byteW, ixSlotB, ixLane, ixSlotW, tw, sbw, add32, shl, shru, andi, r32, i32,
    truncBits]
  interval_cases s <;> nf_simp <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
