-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
public import Lemmas.Flow.OutCore
public import Lemmas.Flow.Regs

@[expose] public section

/-! # The scale bytes of a row

A row's scale load (`ld.shared.v4.b32`) reads four words; the code splits them into the sixteen
scale bytes with `prmt.b32 d, w, 0, 0x777k` (byte `k` of `w`) and `cvt.u16.u32` (`prmt_val`,
`cvt16w_val`). The sixteen bytes as one number are `scWord` (element 0 lowest, `byteAt_scWord_*`),
and the facts of the halfword registers from `b` up are `scaleFacts b sc`: register `b + 2 m`
holds byte `14 - 2 m`, register `b + 2 m + 1` byte `15 - 2 m` (the code's order). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

/-- `prmt.b32 d, a, 0, 0x777k` on a word: its byte `k`. -/
theorem prmt_val {d a w : Nat} {c : Int} (k : Nat) (hc : c = 30576 + k) (hk : k < 4)
    (hw : w < 2 ^ 32) :
    coreF (.int ⟨.prmt none, .int .b 32, false, [some d], [.reg a, .imm 0, .imm c]⟩)
      [a] [.bits 32 (BitVec.ofNat 64 w)] = .ok (.bits 32 (BitVec.ofNat 64 (byteAt w k))) := by
  have hw' : w < 18446744073709551616 := by omega
  subst hc
  simp only [coreF, coreW, lk, oBits, List.zip, List.zipWith, List.lookup, beq_self_eq_true,
    Option.getD_some, truncBits, BitVec.toNat_ofNat, pure, Except.pure, bind, Except.bind,
    Except.ok.injEq, Value.bits.injEq, true_and]
  congr 1
  have h1 : w % 2 ^ 64 = w := Nat.mod_eq_of_lt hw'
  have e0 : ((0 : Int) % ↑((2 : Nat) ^ 64)).toNat % 2 ^ 32 % 2 ^ 64 = 0 := by norm_num
  have e1 : ((30576 + (k : Int)) % ↑((2 : Nat) ^ 64)).toNat % 2 ^ 32 % 2 ^ 64 = 30576 + k := by
    rw [Int.emod_eq_of_lt (by omega) (by norm_num; omega)]
    omega
  simp only [BitVec.toNat_ofInt, h1, e0, e1]
  have hb : w / 2 ^ 56 % 256 = 0 := by
    rw [Nat.div_eq_of_lt (by omega)]
  simp only [prmtBits, byteAt]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
    simp only [zero_mul, zero_add, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceDiv,
      Nat.reduceMod, Nat.div_one, pow_zero, pow_one] <;>
    norm_num [hb] <;> omega

/-- `cvt.u16.u32 d, a` on a byte: the byte as a halfword. -/
theorem cvt16w_val {d a b : Nat} (hb : b < 256) :
    coreF (.cvt { dst := .int .u 16, src := .int .u 32, d := d, srcs := [.reg a] }) [a]
      [.bits 32 (BitVec.ofNat 64 b)] = .ok (bits16 b) := by
  simp [coreF, coreW, cvtW, lk, oBits, oVal, bits16, pure, Except.pure, bind, Except.bind]
  apply BitVec.eq_of_toNat_eq
  simp [truncBits]
  omega

/-- The sixteen scale bytes of a row, from the four words of its scale load. -/
def scWord (w0 w1 w2 w3 : Nat) : Nat := w0 + 256 ^ 4 * (w1 + 256 ^ 4 * (w2 + 256 ^ 4 * w3))

theorem byteAt_high (a b m k : Nat) (ha : a < 256 ^ m) :
    byteAt (a + 256 ^ m * b) (m + k) = byteAt b k := by
  simp only [byteAt, pow_add, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem byteAt_low (a b m k : Nat) (hk : k < m) : byteAt (a + 256 ^ m * b) k = byteAt a k := by
  have e : 256 ^ m * b = 256 ^ k * (256 * (256 ^ (m - k - 1) * b)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← pow_succ, ← pow_add]
    congr 2
    omega
  simp only [byteAt]
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- The halfword facts of the scale registers from `b`, in the code's order. -/
def scaleFacts (b sc : Nat) : List (Nat × Value) :=
  [(b, bits16 (byteAt sc 14)), (b + 1, bits16 (byteAt sc 15)),
    (b + 2, bits16 (byteAt sc 12)), (b + 3, bits16 (byteAt sc 13)),
    (b + 4, bits16 (byteAt sc 10)), (b + 5, bits16 (byteAt sc 11)),
    (b + 6, bits16 (byteAt sc 8)), (b + 7, bits16 (byteAt sc 9)),
    (b + 8, bits16 (byteAt sc 6)), (b + 9, bits16 (byteAt sc 7)),
    (b + 10, bits16 (byteAt sc 4)), (b + 11, bits16 (byteAt sc 5)),
    (b + 12, bits16 (byteAt sc 2)), (b + 13, bits16 (byteAt sc 3)),
    (b + 14, bits16 (byteAt sc 0)), (b + 15, bits16 (byteAt sc 1))]

/-- The bytes of `scWord` by word: element `i`'s byte `k` is byte `4 i + k`. -/
theorem byteAt_scWord {w0 w1 w2 w3 : Nat} (h0 : w0 < 2 ^ 32) (h1 : w1 < 2 ^ 32)
    (h2 : w2 < 2 ^ 32) (k : Nat) (hk : k < 4) :
    byteAt (scWord w0 w1 w2 w3) k = byteAt w0 k ∧
      byteAt (scWord w0 w1 w2 w3) (4 + k) = byteAt w1 k ∧
      byteAt (scWord w0 w1 w2 w3) (4 + (4 + k)) = byteAt w2 k ∧
      byteAt (scWord w0 w1 w2 w3) (4 + (4 + (4 + k))) = byteAt w3 k := by
  have l0 : w0 < 256 ^ 4 := by omega
  have l1 : w1 < 256 ^ 4 := by omega
  have l2 : w2 < 256 ^ 4 := by omega
  simp only [scWord, byteAt_high _ _ _ _ l0, byteAt_high _ _ _ _ l1, byteAt_high _ _ _ _ l2]
  exact ⟨byteAt_low _ _ _ _ hk, byteAt_low _ _ _ _ hk, byteAt_low _ _ _ _ hk, trivial⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
