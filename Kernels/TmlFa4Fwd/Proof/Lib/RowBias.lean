-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Arith32Word
import Lemmas.Flow.Arith32Interval
import Lemmas.Flow.Arith32WordW
import Lemmas.Flow.WordBound
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # A row word from its sum with the O map's row bias -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

theorem shl8_lt (x : BitVec 64) : (shl x 8).toNat < 2 ^ 32 := by
  unfold shl
  split
  · decide
  · exact toNat_r32_lt _

/-- **A word from its sum with the row bias.** -/
theorem row_unbias {s : BitVec 64} {n : Nat} (hs : s.toNat < 2 ^ 32) (hn : n < 2 ^ 31)
    (h : addi s 1073741824 = W (2 ^ 30 + n)) : s = W n := by
  have hi : (i32 1073741824).toNat = 1073741824 := by decide
  have h2 := congrArg BitVec.toNat h
  simp only [addi] at h2
  rw [toNat_W (by omega), show truncBits 32 (r32 s + i32 1073741824) =
    r32 (r32 s + i32 1073741824) from rfl, r32_of_lt hs, toNat_r32, BitVec.toNat_add, hi] at h2
  have h3 : s.toNat = n := by omega
  exact (eq_W s).trans (congrArg W h3)

end PTX.Kernels.TmlFa4Fwd.Proof
