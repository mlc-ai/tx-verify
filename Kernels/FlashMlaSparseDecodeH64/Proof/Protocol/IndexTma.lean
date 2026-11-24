-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases

@[expose] public section

/-! # The index ring's produced values and the TMA producer's reads

The index warp computes the `tma_coord` word of a slot and the raw-KV producer reads the words
its 32 lanes wrote. The two roles define the same arithmetic; this file identifies them and
relates their shared offsets. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma
open PTX

/-- The producer's word at position `p = 2*lane + pair` of a block is the index value of that
slot. -/
theorem coordAt_eq_coordValue (P : Params) (L : Launch) (g b p : Nat) :
    Wg1Tma.coordAt P L g b p = Wg1Index.coordValue P L g b (p / 2) (p % 2) := rfl

/-- Index production and TMA consumption use the same ready and free objects for a block. -/
theorem same_slot {P : Params} {L : Launch} {gi gt : Nat}
    {index : Wg1Index.D} {tma : Wg1Tma.D}
    (hi : Wg1Index.Inv P L gi index) (ht : Wg1Tma.Inv P L gt tma)
    (hib : index.site ≠ .barrier) (htb : tma.site ≠ .barrier) (hte : tma.site ≠ .exit)
    (hblock : index.block = tma.block) :
    Wg1Index.readyOff index.phase = (Mbar.validReady (indexSlot tma.block)).off ∧
      Wg1Index.freeOff index.phase = (Mbar.validFree (indexSlot tma.block)).off ∧
      Wg1Tma.readyOff tma.phase = (Mbar.validReady (indexSlot tma.block)).off ∧
      Wg1Tma.coordFreeOff tma.phase = (Mbar.validFree (indexSlot tma.block)).off ∧
      index.par = tma.par := by
  rw [hi.phase_block hib, ht.phase_eq htb hte, hblock, hi.par_block hib, ht.par_eq htb hte]
  exact ⟨rfl, rfl, rfl, rfl, congrArg (fun b => b / 4 % 2) hblock⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexTma
