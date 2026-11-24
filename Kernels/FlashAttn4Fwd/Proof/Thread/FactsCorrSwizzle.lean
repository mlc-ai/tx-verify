-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Values
public import Kernels.FlashAttn4Fwd.Proof.Thread.Correction
public import Lemmas.Flow.SplitJoin

@[expose] public section

/-! # The staging slots and the correction's staging addresses

Slot `(x, y, k)` of half `hh` of stage `st` reads byte `k` of element `x` of row `y` through the
128-byte swizzle: with a 1024-aligned shared base its address is the row's line
`3072 + 32768 st + 16384 hh + 128 y` plus the 16-byte chunk `x / 8` exchanged by `y % 8`, plus
`(2 x + k) % 16` (`stageLoc_addr`). The correction thread of row `32 k + ln` writes chunk `c` of
its line at `16 (ln % 8 ^^^ c)` (`Correction.stage`), the same swizzle. The words it writes are
packed half-precision pairs (`fw`): when the chunk's values and the row sum `l` are numbers,
byte `b` of word `q` is byte `b % 2` of the product of value `2 q + b / 2` of the chunk with
`1 / l'` (`fw_byte`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The address of a staging slot.** -/
theorem stageLoc_addr {L : Launch} (hsb : L.sharedBase % 1024 = 0) (c st hh x y k : Nat)
    (hx : x < 64) (hk : k < 2) :
    (stageLoc L c st hh x y k).addr = L.sharedBase + (3072 + 32768 * st + 16384 * hh) + 128 * y +
      16 * (x / 8 ^^^ y % 8) + (2 * x + k) % 16 := by
  have h1 : (y * 128 + x * 2 + k) / 128 = y := by omega
  have h2 : (y * 128 + x * 2 + k) / 16 % 8 = x / 8 := by omega
  have h3 : (y * 128 + x * 2 + k) % 16 = (2 * x + k) % 16 := by omega
  have h4 : ((L.sharedBase + (3072 + 32768 * st + 16384 * hh)) / 128 + y) % 8 = y % 8 := by
    omega
  simp only [stageLoc, TensorTile.sharedByte, TensorTile.linearByte, TensorTile.rowBytes,
    TensorTile.count, TensorTile.step, oBox, TensorTile.swizzleWidth, TensorSwizzle.offset,
    TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors, stageBase,
    BitVec.toNat_xor, BitVec.toNat_ofNat]
  have hm : max (64 * 2) 128 = 128 := rfl
  simp only [Matrix.cons_val_zero, ite_self, Nat.add_sub_cancel, Nat.div_one, hm]
  rw [h1, h3, h4]
  rw [show (y * 128 + x * 2 + k) / 16 % 2 ^ 3 = x / 8 by
    rw [show (2 : Nat) ^ 3 = 8 from rfl]; exact h2]
  rw [Nat.mod_eq_of_lt (show y % 8 < 2 ^ 3 by omega)]
  omega

/-- A word read back from its own bytes. -/
theorem rebuild_f32 (l : ℝ) :
    rebuild 3 ((Value.float .f32 l).toBytes.map some) = .ok (.float .f32 l) := by
  simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ,
    pure, Except.pure]

theorem split_join_l {x y : Value} {o : ℝ} (hx : x = .float .f32 o) :
    splitValue 64 (joinValue x y) = (x, y) := by
  subst hx; cases y <;> simp [joinValue, splitValue]

/-- A canonical factor word packed with itself splits into two copies of itself. -/
theorem rcPair_split {d : Correction.D} {x : ℝ} (h : F32Val d.aw x) :
    splitValue 64 (Correction.rcPair d) = (d.aw, d.aw) := by
  rcases h.1 with hv | ⟨b, hb, hlt⟩
  · rw [Correction.rcPair, hv]; simp [joinValue, splitValue]
  · rw [Correction.rcPair, hb]; exact split_join_bits hlt

/-- **The product of pair `q` of a rescaled chunk** on numbers: values `2 q` and `2 q + 1` of the
chunk times a canonical factor word reading as `α`. -/
theorem prodV_rc (d : Correction.D) (q : Nat) {x y α : ℝ}
    (hx : d.o.getD (2 * q) (b32 0) = .float .f32 x)
    (hy : d.o.getD (2 * q + 1) (b32 0) = .float .f32 y) (ha : F32Val d.aw α) :
    Correction.prodV d.o (Correction.rcPair d) q =
      .pair (.float .f32 (x * α)) (.float .f32 (y * α)) := by
  have hrc := rcPair_split ha
  have hw : splitValue 64 (joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0))) =
      (.float .f32 x, .float .f32 y) := by
    rw [hx, hy]; exact split_join_l rfl
  unfold Correction.prodV mulOutV
  exact okVal_of_ok (floatE_mul2_fin (by rw [hw]; exact valFloat_fl x)
    (by rw [hw]; exact valFloat_fl y) (by rw [hrc]; exact ha.2) (by rw [hrc]; exact ha.2))

/-- On a number `l`, the pair the final normalization multiplies with is `1 / l'` twice. -/
theorem split_fcPair (d : Correction.D) {l : ℝ} (hl : valFloat .f32 d.aw = .ok l) :
    splitValue 64 (Correction.fcPair d) =
      (fl (1 / if l = 0 then 1 else l), fl (1 / if l = 0 then 1 else l)) := by
  rw [Correction.fcPair, Correction.recipV_fin hl]
  exact split_join_l rfl

/-- **Word `q` of the normalized chunk** on numbers: the pair of the half-precision products of
values `2 q` and `2 q + 1` with `1 / l'`. -/
theorem fw_eq (d : Correction.D) (q : Nat) {x y l : ℝ}
    (hx : d.o.getD (2 * q) (b32 0) = .float .f32 x)
    (hy : d.o.getD (2 * q + 1) (b32 0) = .float .f32 y) (hl : valFloat .f32 d.aw = .ok l) :
    Correction.fw d q = .pair (h16 (x * (1 / if l = 0 then 1 else l)))
      (h16 (y * (1 / if l = 0 then 1 else l))) := by
  have hc := split_fcPair d hl
  have hw : splitValue 64 (joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0))) =
      (.float .f32 x, .float .f32 y) := by
    rw [hx, hy]; exact split_join_l rfl
  have hm := floatE_mul2_fin (rnd := .rn) (fz := false)
    (va := joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)))
    (vb := Correction.fcPair d)
    (by rw [hw]; exact valFloat_fl x) (by rw [hw]; exact valFloat_fl y)
    (by rw [hc]; exact valFloat_fl _) (by rw [hc]; exact valFloat_fl _)
  have hp : Correction.prodV d.o (Correction.fcPair d) q = .pair
      (.float .f32 (x * (1 / if l = 0 then 1 else l)))
      (.float .f32 (y * (1 / if l = 0 then 1 else l))) := by
    unfold Correction.prodV mulOutV
    exact okVal_of_ok hm
  rw [Correction.fw, cvtOfPair, hp]
  simp only [splitValue]
  rw [cvtPairV_of_valFloat (va := .float .f32 _) (vb := .float .f32 _) (valFloat_fl _)
    (valFloat_fl _), half_of (v := .float .f32 _) (valFloat_fl _),
    half_of (v := .float .f32 _) (valFloat_fl _)]
  rfl

/-- **Byte `b` of a word of the normalized chunk**, on numbers: byte `b % 2` of the product of
value `2 q + b / 2` of the chunk with `1 / l'`. -/
theorem fw_byte (d : Correction.D) (q b : Nat) (hb : b < 4) {x y l o : ℝ}
    (hx : d.o.getD (2 * q) (b32 0) = .float .f32 x)
    (hy : d.o.getD (2 * q + 1) (b32 0) = .float .f32 y) (hl : valFloat .f32 d.aw = .ok l)
    (ho : d.o.getD (2 * q + b / 2) (b32 0) = .float .f32 o) :
    (Correction.fw d q).toBytes[b]? =
      some ((Value.float .f16 (o * (1 / if l = 0 then 1 else l))).byteAt (b % 2)) := by
  rw [fw_eq d q hx hy hl]
  interval_cases b
  · simp only [Nat.reduceDiv, Nat.add_zero, hx, Value.float.injEq, true_and] at ho
    subst ho
    simp [Value.toBytes, Value.byteAt, Value.bytes, h16, FloatFmt.bytes]
  · simp only [Nat.reduceDiv, Nat.add_zero, hx, Value.float.injEq, true_and] at ho
    subst ho
    simp [Value.toBytes, Value.byteAt, Value.bytes, h16, FloatFmt.bytes]
  · simp only [Nat.reduceDiv, hy, Value.float.injEq, true_and] at ho
    subst ho
    simp [Value.toBytes, Value.byteAt, Value.bytes, h16, FloatFmt.bytes]
  · simp only [Nat.reduceDiv, hy, Value.float.injEq, true_and] at ho
    subst ho
    simp [Value.toBytes, Value.byteAt, Value.bytes, h16, FloatFmt.bytes]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
