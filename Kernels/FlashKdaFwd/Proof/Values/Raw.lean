-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Thread.Base
public import Kernels.FlashKdaFwd.Proof.Thread.Rules
public import Kernels.FlashKdaFwd.Data.Recurrence
public import Lemmas.Flow.Bf16Widen
public import Lemmas.Matrix.Move

@[expose] public section

/-! # The raw inputs of the kernel: bfloat16 bit patterns widened to binary32

The kernel reads its two bfloat16 inputs, the values `v` and the gate logits `beta`, as raw
16-bit integers and turns each into a binary32 (`.f32`) number with integer instructions:
`cvt.u32.u16` (zero-extension to 32 bits; outcome function `Rules.zext16E`) and `shl.b32 …, 16`
(outcome function `Rules.shlKE 16`). The shifted word is then used as an `.f32` operand, which
Core reads through the word's bit pattern (`valFloat .f32`). This is exact because a bfloat16
pattern is the upper half of the binary32 pattern of the same number
(`Lemmas/Flow/Bf16Widen.lean`).

A register that holds such an input has one of two shapes, depending on where its bytes came
from:

* bytes of the launch memory, where the specification gives a finite bfloat16 bit pattern
  (`bf16Bits` in `Spec.lean`): a 16-bit integer `.bits 16 n`;
* bytes of a tensor load that was out of bounds, which this model fills with the bfloat16
  *payload* zero `Value.float .bf16 0` (a payload is a value that carries a real number instead
  of bits; its bits, when an integer instruction asks for them, are the encoding of the number).

This file hides the two shapes behind two predicates and proves what the data path needs:

* `Bf16Of v x`: the value `v` has two bytes and its 16 bits are the bfloat16 pattern of the
  finite number `x`. It holds for both shapes (`Bf16Of.bits`, `Bf16Of.zero`), and the two
  widening instructions succeed on such a value and give the `.f32` operand `x`
  (`Bf16Of.widen`).
* `RawPair v x0 x1`: the value `v` of a 32-bit register that `ldmatrix` loaded from `v` holds
  two neighbouring elements; `mov.b32 {lo, hi}, r` (outcome `unpackE 32`) splits it into two
  `Bf16Of` halves. It holds for the 32-bit word of two patterns (`RawPair.bits`), for the pair
  of two payload zeros (`RawPair.zeros`), and for any pair of two `Bf16Of` values
  (`RawPair.pair`); `rebuild_rawPair_bits` and `rebuild_rawPair_zeros` state it for the value a
  load makes of the four bytes (`rebuild 3`).
* The gate: the constants `0fBFB8AA3B` and `0f3F800000` are the numbers
  `Recurrence.multiplier` and `1` (`valFloat_gateMultiplier`, `valFloat_gateOne`), so the
  product and the sum with them are exact (`mulKE_gateMultiplier`, `addKE_gateOne`).
* The gate logit: `beta` is read with a zero-extending 16-bit load into a 32-bit register
  (`ldVal (.zero 32) 16 bs` for the two bytes `bs` read), then shifted. The loaded word is the
  pattern (`ldLogit_bits`) or `0` (`ldLogit_zero`), and its shift is the `.f32` operand of the
  number (`ldLogit_bits_widen`, `ldLogit_zero_widen`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Proof PTX.Flow PTX.WarpMatrix PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

/-! ### One bfloat16 input -/

/-- **The value `v` is the bfloat16 number `x`, held as raw bits**: `v` has two bytes, and the
16 bits an integer instruction reads from it (`readBitsOf 16`) are a pattern `n` that decodes,
as bfloat16, to the finite number `x`. -/
def Bf16Of (v : Value) (x : ℝ) : Prop :=
  v.bytes = 2 ∧ ∃ n < 65536, ∃ q : ℚ, readBitsOf 16 v = .ok (BitVec.ofNat 64 n) ∧
    FloatFmt.bf16.decode n = some q ∧ (q : ℝ) = x

/-- A 16-bit integer whose bits are a finite bfloat16 pattern (what a load of launch memory
gives, `bf16Bits`). -/
theorem Bf16Of.bits {n : Nat} {q : ℚ} {x : ℝ} (hn : n < 65536)
    (hq : FloatFmt.bf16.decode n = some q) (hx : (q : ℝ) = x) :
    Bf16Of (.bits 16 (BitVec.ofNat 64 n)) x :=
  ⟨rfl, n, hn, q, readBitsOf_bits16 hn, hq, hx⟩

/-- The bfloat16 payload zero (what an out-of-bounds tensor load gives): its bits are `0`, the
pattern of the number `0`. -/
theorem Bf16Of.zero : Bf16Of (.float .bf16 0) 0 :=
  ⟨rfl, 0, by norm_num, 0, readBitsOf_bf16_zero, bf16_decode_zero, by norm_num⟩

/-- **`cvt.u32.u16` of a raw bfloat16 input** writes the 32-bit word of its pattern. -/
theorem Bf16Of.zext16 {v : Value} {x : ℝ} (h : Bf16Of v x) :
    ∃ n < 65536, ∃ q : ℚ, Rules.zext16E [v] = .ok (.bits 32 (BitVec.ofNat 64 n)) ∧
      FloatFmt.bf16.decode n = some q ∧ (q : ℝ) = x := by
  obtain ⟨-, n, hn, q, hr, hq, hx⟩ := h
  refine ⟨n, hn, q, ?_, hq, hx⟩
  have ht : truncBits 32 (BitVec.ofNat 64 n) = BitVec.ofNat 64 n :=
    truncBits_ofNat (w := 32) (by omega) (by norm_num)
  cases v with
  | ptr w gn sp off => cases hr
  | _ => simp only [Rules.zext16E, hr, Except.map, ht]

/-- **`shl.b32 …, 16` of the 32-bit word of a finite bfloat16 pattern** succeeds and writes a
four-byte value that is the `.f32` operand of the pattern's number. -/
theorem shlKE_16_word {n : Nat} {q : ℚ} {x : ℝ} (hn : n < 65536)
    (hq : FloatFmt.bf16.decode n = some q) (hx : (q : ℝ) = x) :
    ∃ z, Rules.shlKE 16 [.bits 32 (BitVec.ofNat 64 n)] = .ok z ∧ z.bytes = 4 ∧
      valFloat .f32 z = .ok x := by
  subst hx
  refine ⟨_, Rules.shlKE_16_bits _, rfl, valFloat_shl16_bf16 ?_⟩
  rwa [toNat_ofNat_lt (by omega)]

/-- **The two widening instructions on a raw bfloat16 input.** `cvt.u32.u16` succeeds with a
value `u`, `shl.b32 …, 16` succeeds on `u` with a four-byte value `z`, and `z` is the `.f32`
operand `x`. -/
theorem Bf16Of.widen {v : Value} {x : ℝ} (h : Bf16Of v x) :
    ∃ u z, Rules.zext16E [v] = .ok u ∧ Rules.shlKE 16 [u] = .ok z ∧ z.bytes = 4 ∧
      valFloat .f32 z = .ok x := by
  obtain ⟨n, hn, q, hz, hq, hx⟩ := h.zext16
  obtain ⟨z, hs, hb, hv⟩ := shlKE_16_word hn hq hx
  exact ⟨_, z, hz, hs, hb, hv⟩

/-! ### A register of two bfloat16 inputs -/

/-- **The 32-bit register value `v` holds the two bfloat16 numbers `x0` (low half) and `x1`
(high half) as raw bits**: `v` has four bytes, and `mov.b32 {lo, hi}, v` (outcome `unpackE 32`)
succeeds with two halves that are `Bf16Of` the two numbers. -/
def RawPair (v : Value) (x0 x1 : ℝ) : Prop :=
  v.bytes = 4 ∧ ∃ lo hi, unpackE 32 v = .ok (lo, hi) ∧ Bf16Of lo x0 ∧ Bf16Of hi x1

/-- A packed pair of two raw bfloat16 inputs. -/
theorem RawPair.pair {a b : Value} {x0 x1 : ℝ} (ha : Bf16Of a x0) (hb : Bf16Of b x1) :
    RawPair (.pair a b) x0 x1 :=
  ⟨by simp [Value.bytes, ha.1, hb.1], a, b, Rules.unpackE32_pair ha.1 hb.1, ha, hb⟩

/-- The pair of two payload zeros (a register filled by an out-of-bounds tensor load). -/
theorem RawPair.zeros : RawPair (bf16Pair 0 0) 0 0 := RawPair.pair Bf16Of.zero Bf16Of.zero

/-- The 32-bit word of two finite bfloat16 patterns, `n0` in the low half and `n1` in the high
half (the word `rebuild_bits16_pair_ofNat` gives for their four bytes). -/
theorem RawPair.bits {n0 n1 : Nat} {q0 q1 : ℚ} {x0 x1 : ℝ} (h0 : n0 < 65536) (h1 : n1 < 65536)
    (hq0 : FloatFmt.bf16.decode n0 = some q0) (hq1 : FloatFmt.bf16.decode n1 = some q1)
    (hx0 : (q0 : ℝ) = x0) (hx1 : (q1 : ℝ) = x1) :
    RawPair (.bits 32 (BitVec.ofNat 64 (n0 + 65536 * n1))) x0 x1 := by
  have hlo : truncBits 16 (BitVec.ofNat 64 (n0 + 65536 * n1)) = BitVec.ofNat 64 n0 := by
    simp only [truncBits, BitVec.toNat_ofNat]
    congr 1
    omega
  have hhi : truncBits 16 (BitVec.ofNat 64 ((BitVec.ofNat 64 (n0 + 65536 * n1)).toNat / 2 ^ 16)) =
      BitVec.ofNat 64 n1 := by
    simp only [truncBits, BitVec.toNat_ofNat]
    congr 1
    omega
  refine ⟨rfl, _, _, Rules.unpackE32_bits _, ?_, ?_⟩
  · rw [hlo]; exact Bf16Of.bits h0 hq0 hx0
  · rw [hhi]; exact Bf16Of.bits h1 hq1 hx1

/-- The unpack of a raw pair succeeds, with the halves Core's `splitValue 32` names (the form
the generated run conditions and values use). -/
theorem RawPair.unpack {v : Value} {x0 x1 : ℝ} (h : RawPair v x0 x1) :
    unpackE 32 v = .ok (splitValue 32 v) := by
  obtain ⟨-, lo, hi, hu, -, -⟩ := h
  unfold unpackE at hu ⊢
  split_ifs at hu ⊢
  rfl

/-- The two halves of a raw pair, as `splitValue 32` names them, are raw bfloat16 inputs. -/
theorem RawPair.split {v : Value} {x0 x1 : ℝ} (h : RawPair v x0 x1) :
    Bf16Of (splitValue 32 v).1 x0 ∧ Bf16Of (splitValue 32 v).2 x1 := by
  obtain ⟨-, lo, hi, hu, hlo, hhi⟩ := h
  unfold unpackE at hu
  split_ifs at hu
  injection hu with hu
  rw [hu]
  exact ⟨hlo, hhi⟩

/-- **The four bytes of two finite bfloat16 patterns are loaded as a raw pair** (what `ldmatrix`
puts in a register from launch memory). -/
theorem rebuild_rawPair_bits {n0 n1 : Nat} {q0 q1 : ℚ} {x0 x1 : ℝ} (h0 : n0 < 65536)
    (h1 : n1 < 65536) (hq0 : FloatFmt.bf16.decode n0 = some q0)
    (hq1 : FloatFmt.bf16.decode n1 = some q1) (hx0 : (q0 : ℝ) = x0) (hx1 : (q1 : ℝ) = x1) :
    ∃ v, rebuild 3 [some ((Value.bits 16 (BitVec.ofNat 64 n0)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n0)).byteAt 1),
      some ((Value.bits 16 (BitVec.ofNat 64 n1)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n1)).byteAt 1)] = .ok v ∧ RawPair v x0 x1 :=
  ⟨_, rebuild_bits16_pair_ofNat h0 h1, RawPair.bits h0 h1 hq0 hq1 hx0 hx1⟩

/-- **The four bytes of two payload zeros are loaded as a raw pair of zeros.** -/
theorem rebuild_rawPair_zeros :
    ∃ v, rebuild 3 [bf16Enc 0 0, bf16Enc 0 1, bf16Enc 0 0, bf16Enc 0 1] = .ok v ∧
      RawPair v 0 0 :=
  ⟨_, rebuild_bf16Pair 0 0, RawPair.zeros⟩

/-! ### The gate constants -/

/-- The binary32 pattern `0xBFB8AA3B` is the number `Recurrence.multiplier`: sign `1`, exponent
field `127`, mantissa field `0x38AA3B`, that is `-(2 ^ 23 + 3713595) / 2 ^ 23`. -/
theorem f32Value_gateMultiplier : f32Value 0xBFB8AA3B = some Recurrence.multiplier := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num, Recurrence.multiplier]
  norm_num

/-- The binary32 pattern `0x3F800000` is the number `1`. -/
theorem f32Value_gateOne : f32Value 0x3F800000 = some 1 := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

/-- **The constant `0fBFB8AA3B` of the gate's product is `Recurrence.multiplier`.** -/
theorem valFloat_gateMultiplier :
    valFloat .f32 (Rules.immV 0xBFB8AA3B) = .ok ((Recurrence.multiplier : ℚ) : ℝ) :=
  valFloat_b32 (by norm_num) f32Value_gateMultiplier

/-- **The constant `0f3F800000` of the gate's sum is `1`.** -/
theorem valFloat_gateOne : valFloat .f32 (Rules.immV 0x3F800000) = .ok 1 := by
  have h := valFloat_b32 (b := 0x3F800000) (by norm_num) f32Value_gateOne
  rwa [Rat.cast_one] at h

/-- `mul.ftz.f32 d, a, 0fBFB8AA3B` on a number `x` writes `x * Recurrence.multiplier`. -/
theorem mulKE_gateMultiplier {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) :
    Rules.mulKE 0xBFB8AA3B [va] = .ok (.float .f32 (x * ((Recurrence.multiplier : ℚ) : ℝ))) :=
  Rules.mulKE_fin hx valFloat_gateMultiplier

/-- `add.ftz.f32 d, a, 0f3F800000` on a number `x` writes `x + 1`. -/
theorem addKE_gateOne {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) :
    Rules.addKE 0x3F800000 [va] = .ok (.float .f32 (x + 1)) :=
  Rules.addKE_fin hx valFloat_gateOne

/-! ### The load of a gate logit -/

/-- The zero-extending 16-bit load of the two bytes of the 16-bit integer `n` writes the 32-bit
word `n`. -/
theorem ldLogit_bits {n : Nat} (hn : n < 65536) :
    ldVal (.zero 32) 16 [some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 1)] =
      .ok (.bits 32 (BitVec.ofNat 64 n)) := by
  rw [ldVal, rebuild_bits16]
  exact extendLoaded_zero_bits16 hn

/-- The zero-extending 16-bit load of the two bytes of the payload zero writes the 32-bit word
`0`. -/
theorem ldLogit_zero :
    ldVal (.zero 32) 16 [bf16Enc 0 0, bf16Enc 0 1] = .ok (.bits 32 (BitVec.ofNat 64 0)) := by
  rw [ldVal, show [bf16Enc 0 0, bf16Enc 0 1] = [some ((Value.float .bf16 0).byteAt 0),
    some ((Value.float .bf16 0).byteAt 1)] from rfl, Flow.rebuild_bf16]
  exact extendLoaded_zero_bf16_zero

/-- **The gate logit read from launch memory.** The load of the two bytes of a finite bfloat16
pattern succeeds with a value `u`, `shl.b32 …, 16` succeeds on `u` with a four-byte value `z`,
and `z` is the `.f32` operand of the pattern's number. -/
theorem ldLogit_bits_widen {n : Nat} {q : ℚ} {x : ℝ} (hn : n < 65536)
    (hq : FloatFmt.bf16.decode n = some q) (hx : (q : ℝ) = x) :
    ∃ u z, ldVal (.zero 32) 16 [some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 0),
      some ((Value.bits 16 (BitVec.ofNat 64 n)).byteAt 1)] = .ok u ∧
      Rules.shlKE 16 [u] = .ok z ∧ z.bytes = 4 ∧ valFloat .f32 z = .ok x := by
  obtain ⟨z, hs, hb, hv⟩ := shlKE_16_word hn hq hx
  exact ⟨_, z, ldLogit_bits hn, hs, hb, hv⟩

/-- **The gate logit read from an out-of-bounds tensor load.** The load of the two bytes of the
payload zero succeeds with a value `u`, `shl.b32 …, 16` succeeds on `u` with a four-byte value
`z`, and `z` is the `.f32` operand `0`. -/
theorem ldLogit_zero_widen :
    ∃ u z, ldVal (.zero 32) 16 [bf16Enc 0 0, bf16Enc 0 1] = .ok u ∧
      Rules.shlKE 16 [u] = .ok z ∧ z.bytes = 4 ∧ valFloat .f32 z = .ok 0 := by
  obtain ⟨z, hs, hb, hv⟩ :=
    shlKE_16_word (n := 0) (x := 0) (by norm_num) bf16_decode_zero (by norm_num)
  exact ⟨_, z, ldLogit_zero, hs, hb, hv⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
