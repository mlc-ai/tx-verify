-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RingPhases

@[expose] public section

/-! # The raw ring: TMA destinations and the dequantizer's loads

The raw-KV producer issues 16 four-row gather4 copies at `rawBase buf + 2304 k`; the dequantizer
reads row `rawRow = lr * 16 + group` at `rawBase buf + 576 * rawRow`. Since a gather4 writes four
consecutive 576-byte rows, the two agree byte for byte. The scale bytes are at +512 of each row.

The two roles use the same raw buffer base (`131072 + 36864 * buf`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawTmaDequant
open PTX

theorem rawBase_eq (buf : Nat) : Wg1Tma.rawBase buf = Wg2.rawBase buf := by
  unfold Wg1Tma.rawBase Wg2.rawBase Wg2.rawBufBytes
  rfl

/-- A gather4 destination plus its row within the four-row box is the row's byte offset. -/
theorem issueDst_row (buf r : Nat) :
    Wg1Tma.issueDst buf (r / 4) + 576 * (r % 4) = Wg1Tma.rawBase buf + 576 * r := by
  have hr : r = r % 4 + 4 * (r / 4) := by
    have := Nat.div_add_mod r 4
    omega
  unfold Wg1Tma.issueDst
  rw [hr, Nat.add_mul_div_left _ _ (by decide), Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt (Nat.mod_lt r (by decide)),
    Nat.mod_eq_of_lt (Nat.mod_lt r (by decide))]
  ring

/-- The dequantizer's row `lr` of its group is a whole row of the producer's raw block, at the
same byte. -/
theorem rawRow_addr_eq (L : Launch) (g buf lr : Nat) :
    Wg1Tma.issueDst buf (Wg2.rawRow L g lr / 4) + 576 * (Wg2.rawRow L g lr % 4) =
      Wg2.rawBase buf + Wg2.rawRowOff L g lr := by
  rw [issueDst_row, rawBase_eq]
  unfold Wg2.rawRowOff Wg2.rawRowStride Wg2.rawRow
  omega

/-- Producer and dequantizer agree on the raw ring's buffer, parity, and object offsets. -/
theorem same_slot {P : Params} {L : Launch} {gt gd : Nat}
    {tma : Wg1Tma.D} {dequant : Wg2.D}
    (ht : Wg1Tma.Inv P L gt tma) (hd : Wg2.Inv P L gd dequant)
    (htb : tma.site ≠ .barrier) (hte : tma.site ≠ .exit)
    (hblock : dequant.block = tma.block) :
    Wg1Tma.rawReadyOff tma.buf = (Mbar.rawReady (rawSlot tma.block)).off ∧
      Wg2.rawReadyOff dequant.buf = (Mbar.rawReady (rawSlot tma.block)).off ∧
      Wg1Tma.rawFreeOff tma.buf = (Mbar.rawFree (rawSlot tma.block)).off ∧
      Wg2.rawFreeOff dequant.buf = (Mbar.rawFree (rawSlot tma.block)).off ∧
      dequant.par = tma.rpar := by
  rw [ht.buf_eq htb hte, hd.bufBlock, hblock, hd.parBlock, ht.rpar_eq htb hte]
  have hur : Wg1Tma.rawReadyOff (tma.block % 2) = (Mbar.rawReady (rawSlot tma.block)).off :=
    Wg1Tma.rawReadyOff_eq (rawSlot tma.block)
  have huf : Wg1Tma.rawFreeOff (tma.block % 2) = (Mbar.rawFree (rawSlot tma.block)).off :=
    Wg1Tma.rawFreeOff_eq (rawSlot tma.block)
  exact ⟨hur, hur, huf, huf, congrArg (fun b => b / 2 % 2) hblock⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawTmaDequant
