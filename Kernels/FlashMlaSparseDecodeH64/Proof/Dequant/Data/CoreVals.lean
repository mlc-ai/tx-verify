-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
public import Lemmas.Flow.OutCore

@[expose] public section

/-! # Core's values of the dequantizer's integer instructions and moves

The generated runs (`Gen/Runs*.lean`) state each integer instruction's value as `coreF` of its
decoded instruction on its sources' values. On the values a chunk has, these are: the halfwords
of the raw word (`half_val`: `cvt.u16.u64` after `shr.u64` by `16 j`), the scale byte the
selector picks (`sel_val`), its broadcast into both halves (`dup_val`: `mul.lo.s16` by 257), and
the 128-bit join of two packed words (`pack_val`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Flow
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section

/-- `selp.b16 d, a, b, p` on two halfwords: the one the predicate picks. -/
theorem sel_val {d a b p lo hi : Nat} (q : Bool) (hab : a ≠ b) (hap : a ≠ p) (hbp : b ≠ p) :
    coreF (.int ⟨.selp, .int .b 16, false, [some d], [.reg a, .reg b, .reg p]⟩) [a, b, p]
      [bits16 hi, bits16 lo, .pred q] = .ok (bits16 (if q then hi else lo)) := by
  have e1 : (p == a) = false := by simpa using hap.symm
  have e2 : (p == b) = false := by simpa using hbp.symm
  have e3 : (b == a) = false := by simpa using hab.symm
  cases q <;> simp [coreF, coreW, lk, oVal, List.lookup, e1, e2, e3, bits16, DType.width, pure,
    Except.pure] <;> rfl

/-- `mul.lo.s16 d, a, 257` on a byte: the byte in both halves. -/
theorem dup_val {d a s : Nat} (hs : s < 256) :
    coreF (.int ⟨.mul .lo, .int .s 16, false, [some d], [.reg a, .imm 257]⟩) [a]
      [bits16 s] = .ok (bits16 (s + 256 * s)) := by
  have l1 : s * 257 < 65536 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 257 (Nat.le_of_lt_succ hs)) (by norm_num)
  simp [coreF, coreW, lk, oBits, bits16, DType.width, pure, Except.pure, bind, Except.bind]
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, BitVec.toNat_mul, Nat.mod_eq_of_lt l1]
  omega

/-- `mov.b128 d, {a, b}` of two 64-bit values: their join. -/
theorem pack_val {d a b : Nat} (x y : Value) (hab : a ≠ b) (hx : x.bytes = 8)
    (hy : y.bytes = 8) :
    coreF (.move ⟨.pack, .int .b 128, [some d], [.reg a, .reg b]⟩) [a, b] [x, y] =
      .ok (joinValue x y) := by
  have e3 : (b == a) = false := by simpa using hab.symm
  simp [coreF, coreW, lk, oVal, List.lookup, e3, hx, hy, DType.width, pure, Except.pure, bind,
    Except.bind]

/-- `shr.u64 d, a, k` on a 64-bit word. -/
theorem shr_val {d a w : Nat} (k : Nat) (hk : k < 64) (hw : w < 2 ^ 64) :
    coreF (.int ⟨.shr, .int .u 64, false, [some d], [.reg a, .imm k]⟩) [a]
      [.bits 64 (BitVec.ofNat 64 w)] = .ok (.bits 64 (BitVec.ofNat 64 (w / 2 ^ k))) := by
  have hk' : (truncBits 32 (BitVec.ofNat 64 k)).toNat = k := by
    simp [truncBits]; omega
  simp [coreF, coreW, lk, oBits, DType.width, DType.kind?, pure, Except.pure, bind, Except.bind,
    hk', show ¬ 64 ≤ k by omega]
  apply BitVec.eq_of_toNat_eq
  have hw' : w < 18446744073709551616 := hw
  simp [truncBits, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hw', Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hw')]

/-- `cvt.u16.u64 d, a` on a 64-bit word: its low halfword. -/
theorem cvt16_val {d a w : Nat} (hw : w < 2 ^ 64) :
    coreF (.cvt { dst := .int .u 16, src := .int .u 64, d := d, srcs := [.reg a] }) [a]
      [.bits 64 (BitVec.ofNat 64 w)] = .ok (bits16 (w % 65536)) := by
  have hw' : w < 18446744073709551616 := hw
  simp [coreF, coreW, cvtW, lk, oBits, oVal, bits16, pure, Except.pure, bind, Except.bind]
  apply BitVec.eq_of_toNat_eq
  simp [truncBits, Nat.mod_eq_of_lt hw']


/-- Halfword `j` of the word `w`, as its two bytes. -/
theorem half_eq (w j : Nat) :
    bits16 (w / 2 ^ (16 * j) % 65536) = bits16 (byteAt w (2 * j) + 256 * byteAt w (2 * j + 1)) := by
  rw [← rawPairBits_eq w j]
  rfl

theorem div_lt {w : Nat} (hw : w < 2 ^ 64) (k : Nat) : w / 2 ^ k < 2 ^ 64 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) hw

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
