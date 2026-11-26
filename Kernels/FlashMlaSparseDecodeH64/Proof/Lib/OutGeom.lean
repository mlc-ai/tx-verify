-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0

@[expose] public section

/-! # An output slot's source byte is one staging store's word

The output tensor store of warp `w` and chunk `c` reads slot `(x, y, z)` (column, row, byte) at
`16384 w + wg0OutOff c + 128 y + 16 ((x / 8) ^^^ y % 8) + 2 (x % 8) + z` of the staging area; the
staging store `k`, element `el` of thread `t` writes the four bytes at
`16384 (t / 64) + 128 (t % 64) + 16 (k ^^^ t % 8) + wg0OutOff c' + 4 el`. When the byte `s` of the
word is the slot's byte, the thread is `64 w + y`, the chunk and the swizzled 16-byte chunk
agree, and the word is element `(2 (x % 8) + z) / 4` (`out_geom`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- **The staging word of a slot's byte.** -/
theorem out_geom {w c c' x y z t k el s : Nat} (hw : w < 2) (hc : c < 4) (hc' : c' < 4)
    (hx : x < 64) (hy : y < 64) (hz : z < 2) (ht : t < 128) (hk : k < 8) (hel : el < 4)
    (hs : s < 4)
    (h : 16384 * w + MemRow.wg0OutOff c + (128 * y + 16 * ((x / 8) ^^^ (y % 8)) +
        2 * (x % 8) + z) =
      16384 * (t / 64) + 128 * (t % 64) + 16 * (k ^^^ t % 8) + MemRow.wg0OutOff c' +
        4 * el + s) :
    t / 64 = w ∧ t % 64 = y ∧ c' = c ∧ k = x / 8 ∧ el = (2 * (x % 8) + z) / 4 ∧
      s = (2 * (x % 8) + z) % 4 := by
  have hA : (x / 8) ^^^ (y % 8) < 8 := MemRow.swz_lt (t := y) (by omega)
  have hB : k ^^^ t % 8 < 8 := MemRow.swz_lt hk
  have hcc : c' = c ∧ t / 64 = w := by
    interval_cases c <;> interval_cases c' <;> interval_cases w <;>
      simp only [MemRow.wg0OutOff, List.getD_cons_zero, List.getD_cons_succ] at h <;> omega
  obtain ⟨rfl, hw'⟩ := hcc
  have hty : t % 64 = y := by omega
  have hA' : (x / 8) ^^^ (y % 8) = k ^^^ t % 8 := by omega
  have hm : t % 8 = y % 8 := by omega
  rw [hm] at hA'
  have hk' : k = x / 8 := by
    have := congrArg (· ^^^ (y % 8)) hA'
    simpa [Nat.xor_assoc] using this.symm
  refine ⟨hw', hty, rfl, hk', ?_, ?_⟩ <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
