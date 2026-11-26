-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.EmuStep
public import Lemmas.Tcgen05.FloatBits

@[expose] public section

/-! # A bfloat16 bit pattern widened to binary32 with integer instructions

A proof tool. Compiled code often widens a bfloat16 number (`.bf16`: 1 sign bit, 8 exponent bits,
7 mantissa bits) to binary32 (`.f32`: 1 sign bit, 8 exponent bits, 23 mantissa bits) without a
floating instruction: it loads the 16 bits as an integer, zero-extends them (`cvt.u32.u16` or a
zero-extending load), shifts them left by 16 (`shl.b32 …, 16`) and uses the 32-bit word as an
`.f32` operand. This is exact, because a bfloat16 pattern is the upper half of the binary32
pattern of the same number: the sign and exponent fields coincide and the 7 mantissa bits are
the top 7 of the 23.

Core reads a floating operand from an integer word through the word's bit pattern (`valFloat`,
which decodes the pattern with `FloatFmt.decode`). The lemmas here give that reading for the
shifted word, and the two facts about loaded bytes such code needs.

* **The payload zero.** A *payload* is a value `Value.float fmt x` that carries the real number
  `x` instead of bits; its bits, when an integer instruction asks for them, are
  `FloatFmt.encode x`. The payload `0` has the bits `0` (`encode_zero`, `bf16_encode_zero`,
  `bitPattern_bf16_zero`), which decode to the number `0` (`bf16_decode_zero`).
* **Widening.** `f32_decode_shl16`: the pattern `n * 65536` decodes as binary32 to what `n`
  decodes to as bfloat16 (`magnitude_shift` is the reason: appending `k` zero bits to the
  mantissa field does not change a magnitude). `valFloat_bf16_shl16` and `valFloat_shl16_bf16`
  state it for the word a register holds, the latter in the form the shift instruction
  produces (`shlE`, the outcome of `shl.b32`; `truncBits w` keeps the low `w` bits);
  `shlE_16_bf16` is the instruction's outcome.
* **Reading 16 bits.** `readBitsOf 16 v` is what an integer instruction reads from a register
  holding `v`, and `extendLoaded (.zero 32) 16 v` is the register value after a zero-extending
  16-bit load returned `v`; both are computed for a 16-bit integer and for the payload zero.
* **Loaded bytes.** `rebuild 3 bs` is the value a load makes of the bytes `bs` it read. The two
  bytes of one 16-bit integer or of one bfloat16 payload give that value back (`rebuild_bits16`,
  `rebuild_bf16`); the four bytes of two 16-bit integers give one 32-bit word with the first
  integer in its low half (`rebuild_bits16_pair`, `rebuild_bits16_pair_ofNat`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-! ### The payload zero -/

/-- **The payload of the number `0` has the bits `0`** in every format: `0` is the magnitude of
the field `0`, and a zero is written as `+0`. -/
theorem encode_zero (fmt : FloatFmt) : fmt.encode 0 = 0 := by
  have h := encode_magnitude fmt (F := 0) false (Nat.zero_le _) (by simp)
  simpa [magnitude_zero] using h

/-- The bfloat16 payload of `0` has the bits `0`. -/
theorem bf16_encode_zero : FloatFmt.bf16.encode 0 = 0 := encode_zero .bf16

/-- The bit pattern an integer instruction or a byte read sees in the bfloat16 payload `0`. -/
theorem bitPattern_bf16_zero : (Value.float .bf16 0).bitPattern = some 0 := by
  simp only [Value.bitPattern, bf16_encode_zero]

/-- The bfloat16 pattern `0` is the number `0`. -/
theorem bf16_decode_zero : FloatFmt.bf16.decode 0 = some 0 := by
  simp [FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal, FVal.num]

/-! ### The binary32 number of a widened pattern -/

/-- **Appending `k` zero bits to the mantissa field keeps the magnitude.** `Layout.magnitude eb mb
F` is the magnitude of the exponent-and-mantissa field `F` of a format with `eb` exponent and
`mb` mantissa bits. The field `F * 2 ^ k` of the format with `mb + k` mantissa bits has the same
exponent field and the mantissa `2 ^ k` times as large, in units `2 ^ k` times as small. -/
theorem magnitude_shift (eb mb k F : Nat) :
    Layout.magnitude eb (mb + k) (F * 2 ^ k) = Layout.magnitude eb mb F := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hd : F * 2 ^ k / 2 ^ (mb + k) = F / 2 ^ mb := by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ hk]
  have hm : F * 2 ^ k % 2 ^ (mb + k) = F % 2 ^ mb * 2 ^ k := by
    rw [Nat.pow_add, Nat.mul_mod_mul_right]
  have hz : ∀ c : ℤ, (2 : ℚ) ^ (c - ((mb + k : ℕ) : ℤ)) * 2 ^ k = (2 : ℚ) ^ (c - (mb : ℤ)) := by
    intro c
    rw [← zpow_natCast (2 : ℚ) k, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    push_cast
    ring
  simp only [Layout.magnitude, hd, hm]
  split_ifs with he
  · rw [← hz]; push_cast; ring
  · rw [← hz]; push_cast; ring

/-- The finite decoder of a format reads only the bits of the format's width. -/
theorem decode_mod_width (fmt : FloatFmt) (n : Nat) :
    fmt.decode (n % 2 ^ fmt.layout.width) = fmt.decode n := by
  simp only [FloatFmt.decode, Layout.decode, Nat.mod_mod]

/-- **A bfloat16 pattern is the upper half of the binary32 pattern of the same number**: the
pattern `n` moved up by 16 bits decodes as binary32 exactly as `n` decodes as bfloat16 (the same
number, and no number for an infinity or a NaN). No bound on `n` is needed, since both decoders
read only the low 16 bits of `n`. -/
theorem f32_decode_shl16 (n : Nat) :
    FloatFmt.f32.decode (n * 65536) = FloatFmt.bf16.decode n := by
  have hmag : ∀ F, FloatFmt.f32.magnitude (F * 65536) = FloatFmt.bf16.magnitude F :=
    fun F => magnitude_shift 8 7 16 F
  have h1 : n * 65536 % 2147483648 = n % 32768 * 65536 := by omega
  have h2 : n % 32768 * 65536 / 8388608 = n % 32768 / 128 := by omega
  have h3 : n * 65536 / 2147483648 % 2 = n / 32768 % 2 := by omega
  rw [FloatFmt.decode_eq, FloatFmt.decode_eq]
  simp only [FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.layout, Nat.reducePow, Nat.reduceAdd,
    Nat.reduceSub, ne_eq, reduceCtorEq, not_false_eq_true, true_or, and_true, h1, h2, h3, hmag]
  rfl

/-- A 32-bit word whose low 32 bits are the bfloat16 pattern `n` in the upper half and zeros in
the lower half reads, as an `.f32` operand, as the number of `n`. -/
theorem valFloat_f32_of_bf16_high {y : BitVec 64} {n : Nat} {q : ℚ}
    (hy : y.toNat % 2 ^ 32 = n % 65536 * 65536) (hq : FloatFmt.bf16.decode n = some q) :
    valFloat .f32 (.bits 32 y) = .ok (q : ℝ) := by
  have hd : f32Value y.toNat = some q := by
    rw [f32Value, ← decode_mod_width .f32 y.toNat,
      show (2 : ℕ) ^ FloatFmt.f32.layout.width = 2 ^ 32 from rfl, hy, f32_decode_shl16,
      ← hq]
    exact decode_mod_width .bf16 n
  have h := valFloat_b32 y.isLt hd
  rwa [b32, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

/-- **The widening lemma.** The word `n * 65536`, for a bfloat16 pattern `n` of the finite number
`q`, is the `.f32` operand `q`. -/
theorem valFloat_bf16_shl16 {n : Nat} {q : ℚ} (hq : FloatFmt.bf16.decode n = some q) :
    valFloat .f32 (.bits 32 (BitVec.ofNat 64 (n * 65536))) = .ok (q : ℝ) := by
  refine valFloat_f32_of_bf16_high ?_ hq
  rw [BitVec.toNat_ofNat]
  omega

/-- **The widening lemma in the form `shl.b32 …, 16` produces** (`shlE`): the low 32 bits of the
word `x` shifted left by 16, kept to 32 bits, are the `.f32` operand whose number is the bfloat16
number of the low 16 bits of `x`. -/
theorem valFloat_shl16_bf16 {x : BitVec 64} {q : ℚ}
    (hq : FloatFmt.bf16.decode x.toNat = some q) :
    valFloat .f32 (.bits 32 (truncBits 32 (truncBits 32 x <<< 16))) = .ok (q : ℝ) := by
  refine valFloat_f32_of_bf16_high ?_ hq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- **`shl.b32 d, a, 16` on a word whose low 16 bits are a finite bfloat16 pattern** succeeds,
and writes a four-byte value that is the `.f32` operand of the same number. -/
theorem shlE_16_bf16 {w : Nat} {x : BitVec 64} {q : ℚ}
    (hq : FloatFmt.bf16.decode x.toNat = some q) :
    ∃ z, shlE (.bits w x) 16 = .ok z ∧ z.bytes = 4 ∧ valFloat .f32 z = .ok (q : ℝ) :=
  ⟨_, rfl, rfl, valFloat_shl16_bf16 hq⟩

/-! ### Reading 16 bits -/

/-- An integer instruction reads the 16-bit integer `n` as `n`. -/
theorem readBitsOf_bits16 {n : Nat} (hn : n < 65536) :
    readBitsOf 16 (.bits 16 (BitVec.ofNat 64 n)) = .ok (BitVec.ofNat 64 n) := by
  simp only [readBitsOf, truncBits_ofNat (w := 16) hn (by norm_num)]
  rfl

/-- An integer instruction reads the bfloat16 payload `0` as the bits `0`. -/
theorem readBitsOf_bf16_zero :
    readBitsOf 16 (.float .bf16 0) = .ok (BitVec.ofNat 64 0) := by
  simp only [readBitsOf, bitPattern_bf16_zero]
  rfl

/-- A zero-extending 16-bit load into a 32-bit register (`ld.u16` or `ld.b16` with a `.b32`
destination) of the 16-bit integer `n` writes the 32-bit word `n`. -/
theorem extendLoaded_zero_bits16 {n : Nat} (hn : n < 65536) :
    extendLoaded (.zero 32) 16 (.bits 16 (BitVec.ofNat 64 n)) =
      .ok (.bits 32 (BitVec.ofNat 64 n)) := by
  simp only [extendLoaded, Value.bitPattern, MemExt.extendBits, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, truncBits_ofNat (w := 16) hn (by norm_num)]
  rfl

/-- A zero-extending 16-bit load into a 32-bit register of the bfloat16 payload `0` writes the
32-bit word `0`. -/
theorem extendLoaded_zero_bf16_zero :
    extendLoaded (.zero 32) 16 (.float .bf16 0) = .ok (.bits 32 (BitVec.ofNat 64 0)) := by
  simp only [extendLoaded, bitPattern_bf16_zero, MemExt.extendBits]
  rfl

/-! ### Loaded bytes -/

/-- The two bytes of one stored 16-bit integer are loaded as that integer. -/
theorem rebuild_bits16 (a : BitVec 64) :
    rebuild 3 [some ((Value.bits 16 a).byteAt 0), some ((Value.bits 16 a).byteAt 1)] =
      .ok (.bits 16 a) := by
  simp [rebuild, Value.bytes, Value.toBytes, Value.byteAt, List.range_succ, pure, Except.pure]

/-- The two bytes of one stored bfloat16 payload are loaded as that payload. -/
theorem rebuild_bf16 (x : ℝ) :
    rebuild 3 [some ((Value.float .bf16 x).byteAt 0), some ((Value.float .bf16 x).byteAt 1)] =
      .ok (.float .bf16 x) := by
  simp [rebuild, Value.bytes, FloatFmt.bytes, Value.toBytes, Value.byteAt, List.range_succ, pure,
    Except.pure]

/-- **Four bytes of two 16-bit integers are loaded as one 32-bit word**, the first integer in the
low half and the second in the high half (memory is little-endian). Only the low 16 bits of the
stored integers `a` and `b` are in their bytes. -/
theorem rebuild_bits16_pair (a b : BitVec 64) :
    rebuild 3 [some ((Value.bits 16 a).byteAt 0), some ((Value.bits 16 a).byteAt 1),
      some ((Value.bits 16 b).byteAt 0), some ((Value.bits 16 b).byteAt 1)] =
      .ok (.bits 32 (BitVec.ofNat 64 (a.toNat % 65536 + 65536 * (b.toNat % 65536)))) := by
  have hx : a.toNat % 256 + 256 * (a.toNat / 256 % 256 + 256 * (b.toNat % 256 +
      256 * (b.toNat / 256 % 256))) = a.toNat % 65536 + 65536 * (b.toNat % 65536) := by omega
  simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte, Value.bytes,
    Value.toBytes, Value.byteAt, Value.bitPattern, List.range_succ, bind, Option.bind, pure,
    Except.pure, hx]

/-- The four bytes of the 16-bit integers `n0` and `n1` are loaded as the word
`n0 + 65536 * n1`. -/
theorem rebuild_bits16_pair_ofNat {n0 n1 : Nat} (h0 : n0 < 65536) (h1 : n1 < 65536) :
    rebuild 3 [some ((Value.bits 16 (BitVec.ofNat 64 n0)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n0)).byteAt 1),
      some ((Value.bits 16 (BitVec.ofNat 64 n1)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n1)).byteAt 1)] =
      .ok (.bits 32 (BitVec.ofNat 64 (n0 + 65536 * n1))) := by
  rw [rebuild_bits16_pair, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  congr 3
  omega

end

end PTX.Flow
