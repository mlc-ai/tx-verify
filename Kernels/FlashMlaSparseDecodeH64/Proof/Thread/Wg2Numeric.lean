-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions

@[expose] public section

/-! # Numeric operations of the FlashMLA dequantizer

The two packed widening conversions preserve their finite input values. The multiplication
uses the kernel's exact-product rule and the store packs the results in little-endian order.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2.Numeric
open PTX Assumptions
noncomputable section

theorem e4m3_decode_real {b : Nat} (hb : b < 256) (hpos : b ≠ 127) (hneg : b ≠ 255) :
    (FloatFmt.e4m3.decode b).map (fun n : ℚ => (n : ℝ)) = some (e4m3Val b) := by
  rw [FloatFmt.decode_eq]
  change (if b % 128 / 8 = 15 ∧ (.e4m3 ≠ FloatFmt.e4m3 ∨ b % 128 % 8 = 7) then none
    else some (if b / 128 % 2 = 0 then FloatFmt.e4m3.magnitude (b % 128)
      else -FloatFmt.e4m3.magnitude (b % 128))).map (fun n : ℚ => (n : ℝ)) = _
  have hcase : ¬ (b % 128 / 8 = 15 ∧ b % 128 % 8 = 7) := by omega
  have hsign : b / 128 % 2 = b / 128 := Nat.mod_eq_of_lt (by omega)
  have he : b % 128 / 8 = b / 8 % 16 := by omega
  have hm : b % 128 % 8 = b % 8 := by omega
  simp only [ne_eq, not_true_eq_false, false_or, hcase, ↓reduceIte, hsign]
  have hmag : ((FloatFmt.e4m3.magnitude (b % 128) : ℚ) : ℝ) =
      if b / 8 % 16 = 0 then ((b % 8 : Nat) : ℝ) / 8 * (2 : ℝ) ^ (-6 : ℤ)
      else (1 + ((b % 8 : Nat) : ℝ) / 8) * (2 : ℝ) ^ ((b / 8 % 16 : Nat) - (7 : ℤ)) := by
    rw [FloatFmt.magnitude_eq]
    simp only [show FloatFmt.e4m3.mantBits = 3 from rfl, show FloatFmt.e4m3.bias = 7 from rfl,
      Nat.reducePow, he, hm]
    split_ifs with hz
    · norm_num
      ring
    · norm_num
      rw [show ((b : ℤ) / 8 % 16) - 7 - 3 = ((b : ℤ) / 8 % 16) - 7 + (-3) by omega,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
  unfold e4m3Val
  obtain hs | hs : b / 128 = 0 ∨ b / 128 = 1 := by omega
  · simp only [hs, Nat.reduceEqDiff, ↓reduceIte, Option.map_some, Option.some.injEq, one_mul]
    exact hmag
  · simp only [hs, Nat.reduceEqDiff, ↓reduceIte, Option.map_some, Option.some.injEq,
      neg_one_mul, Rat.cast_neg, hmag]
    split_ifs <;> ring

/-- The exact narrowing-free conversion of a finite e4m3 byte, preserving signed zero. -/
def e4m3Widened (b : Nat) : Value :=
  if b = 128 then .bits 16 (BitVec.ofNat 64 32768) else .float .bf16 (e4m3Val b)

def pairCvt (sf : FType) (src dst : Nat) : CvtInstr where
  dst := .packed (.float .bf16) 2
  src := .packed (.float sf) 2
  rnd := some .rn
  d := dst
  srcs := [.reg src]

theorem e4m3_decode_abs (b : Fin 256) :
    |(FloatFmt.e4m3.decode b.val).getD 0| ≤ FloatFmt.bf16.layout.maxNorm := by
  have h : ∀ a : Fin 256,
      |(FloatFmt.e4m3.decode a.val).getD 0| ≤ FloatFmt.bf16.layout.maxNorm := by
    decide +kernel
  exact h b

theorem e4m3Widened_real {b : Nat} : valFloat .bf16 (e4m3Widened b) = .ok (e4m3Val b) := by
  by_cases h : b = 128
  · subst b
    have hc : classify .bf16 (.bits 16 (BitVec.ofNat 64 32768)) = .ok (.zero true) :=
      classify_bits (fmt := .bf16) (by decide) (by decide)
    rw [e4m3Widened, ite_eq_left rfl, valFloat_of_classify (by intro f x hx; cases hx) hc]
    norm_num [e4m3Val, FVal.finite, pure, Except.pure]
  · rw [e4m3Widened, ite_eq_right h, valFloat_float]

theorem classify_e4m3_zero {b : Nat} {sg : Bool} (hb : b < 256)
    (hz : FloatFmt.e4m3.layout.decode b = some (.zero sg)) :
    b = if sg then 128 else 0 := by
  have h : ∀ a : Fin 256, ∀ s : Bool, FloatFmt.e4m3.layout.decode a.val = some (.zero s) →
      a.val = if s then 128 else 0 := by decide +kernel
  exact h ⟨b, hb⟩ sg hz

theorem e4m3_widen {b : Nat} (hb : b < 256) (hpos : b ≠ 127) (hneg : b ≠ 255)
    (src dst : Nat) :
    (do
        let x ← cvtElem .e4m3 (.bits 8 (BitVec.ofNat 64 b))
        let y ← widenElem (pairCvt .e4m3 src dst) .bf16 FloatFmt.bf16.layout false x
        pure (y.toValue .bf16) : Exec Value) = .ok (e4m3Widened b) := by
  have hd := e4m3_decode_real hb hpos hneg
  rw [FloatFmt.decode] at hd
  have hfmt : FType.e4m3.fmt? = some FloatFmt.e4m3 := rfl
  rw [cvtElem_fmt hfmt]
  cases h : FloatFmt.e4m3.layout.decode b with
  | none => simp [h] at hd
  | some x =>
    have hc : classify .e4m3 (.bits 8 (BitVec.ofNat 64 b)) = .ok x :=
      classify_bits (fmt := .e4m3) (by omega) h
    rw [hc]
    cases x with
    | inf | nan => simp [h, FVal.num] at hd
    | zero sg =>
      have hzero := classify_e4m3_zero hb h
      cases sg <;> subst b <;> simp [widenElem, pairCvt, cvtSpecial, cvtFinish, FVal.toValue,
        e4m3Widened, FloatFmt.bytes, FloatFmt.layout, Layout.signPattern,
        Layout.width, bind, Except.bind, pure, Except.pure];
        norm_num [e4m3Val]
    | fin q =>
      have hq : (q : ℝ) = e4m3Val b := by simpa [h, FVal.num] using hd
      have hb128 : b ≠ 128 := by intro he; subst b; change some (FVal.zero true) = _ at h; cases h
      have hle : |q| ≤ FloatFmt.bf16.layout.maxNorm := by
        have ha := e4m3_decode_abs ⟨b, hb⟩
        simpa [FloatFmt.decode, h, FVal.num] using ha
      simp [widenElem_fin hle, cvtFinish, pairCvt, FVal.toValue, e4m3Widened, hb128, hq,
        bind, Except.bind, pure, Except.pure]

def bits16 (n : Nat) : Value := .bits 16 (BitVec.ofNat 64 n)

theorem splitValue_bits16_pair {a b : Nat} (ha : a < 256) (hb : b < 256) :
    splitValue 16 (bits16 (a + 256 * b)) =
      (.bits 8 (BitVec.ofNat 64 a), .bits 8 (BitVec.ofNat 64 b)) := by
  have hw : a + 256 * b < 18446744073709551616 := by omega
  have he : (a + 256 * b) % 256 = a := by omega
  have hd : (a + 256 * b) / 256 = b := by omega
  simp [bits16, splitValue, truncBits, BitVec.toNat_ofNat, he]
  rw [Nat.mod_eq_of_lt hw, hd, Nat.mod_eq_of_lt hb]

variable {L : Launch} {g : Nat} {t : TState}

theorem e4m3_execCvt {src dst a b : Nat} (hr : t.regs src = some (bits16 (a + 256 * b)))
    (ha : a < 256) (hb : b < 256) (ha1 : a ≠ 127) (ha2 : a ≠ 255) (hb1 : b ≠ 127) (hb2 : b ≠ 255) :
    execCvt L g t (pairCvt .e4m3 src dst) =
      .ok (next (setReg t dst (.pair (e4m3Widened a) (e4m3Widened b)))) := by
  have hpair {x : Nat} (hx : x < 256) (hx1 : x ≠ 127) (hx2 : x ≠ 255) :
      ∃ f v : FVal, cvtElem .e4m3 (.bits 8 (BitVec.ofNat 64 x)) = .ok f ∧
        widenElem (pairCvt .e4m3 src dst) .bf16 FloatFmt.bf16.layout false f = .ok v ∧
        v.toValue .bf16 = e4m3Widened x := by
    have hh := e4m3_widen hx hx1 hx2 src dst
    cases hf : cvtElem .e4m3 (.bits 8 (BitVec.ofNat 64 x)) with
    | error err => simp [hf, bind, Except.bind] at hh
    | ok f =>
      cases hv : widenElem (pairCvt .e4m3 src dst) .bf16 FloatFmt.bf16.layout false f with
      | error err => simp [hf, hv, bind, Except.bind] at hh
      | ok v => exact ⟨f, v, rfl, hv, by simpa [hf, hv, bind, Except.bind, pure, Except.pure]
          using hh⟩
  obtain ⟨fa, xa, hfa, hxa, ha'⟩ := hpair ha ha1 ha2
  obtain ⟨fb, xb, hfb, hxb, hb'⟩ := hpair hb hb1 hb2
  have hw := splitValue_bits16_pair ha hb
  simp only [execCvt, pairCvt, readValue, readReg, hr, FType.layout?, FType.fmt?,
    CvtRnd.mode?, Bind.bind, Except.bind, Pure.pure, Except.pure, Option.bind_some,
    Option.map_some, reduceCtorEq, ↓reduceIte, or_self, false_or, cvtScales]
  simp only [packedElems, bits16] at hw ⊢
  rw [hw]
  simp only [Value.bytes, Nat.reduceDiv, ↓reduceIte, Bind.bind, Except.bind, Pure.pure,
    Except.pure, hfa, hfb]
  change (do
    let lo ← widenElem (pairCvt .e4m3 src dst) .bf16 FloatFmt.bf16.layout false fa
    let hi ← widenElem (pairCvt .e4m3 src dst) .bf16 FloatFmt.bf16.layout false fb
    let v ← cvtPack .bf16 FloatFmt.bf16.layout lo hi
    pure (next (setReg t dst v)) : Exec TState) = _
  simp [hxa, hxb, ha', hb', bind, Except.bind, pure, Except.pure, cvtPack, FType.fmt?]

def ue8m0Rat (a : Nat) : ℚ := (2 : ℚ) ^ ((a : ℤ) - 127)

theorem ue8m0_rat_bound {a : Nat} (ha : a < 255) :
    |ue8m0Rat a| ≤ FloatFmt.bf16.layout.maxNorm := by
  have ht : (2 : ℚ) ^ (127 : ℤ) ≤ FloatFmt.bf16.layout.maxNorm := by decide +kernel
  have he : (a : ℤ) - 127 ≤ 127 := by omega
  have hp : 0 ≤ ue8m0Rat a := by unfold ue8m0Rat; positivity
  rw [abs_of_nonneg hp]
  exact (zpow_le_zpow_right₀ (by decide : (1 : ℚ) ≤ 2) he).trans ht

theorem ue8m0_rat_real (a : Nat) : ((ue8m0Rat a : ℚ) : ℝ) = ue8m0Val a := by
  simp [ue8m0Rat, ue8m0Val]

theorem ue8m0_execCvt_pos {src dst a : Nat} (hr : t.regs src = some (bits16 (a + 256 * a)))
    (ha0 : 0 < a) (ha : a < 255) :
    execCvt L g t (pairCvt .ue8m0 src dst) =
      .ok (next (setReg t dst (Assumptions.bf16Pair (ue8m0Val a) (ue8m0Val a)))) := by
  have hw := splitValue_bits16_pair (show a < 256 by omega) (show a < 256 by omega)
  have hval : (Value.bits 8 (BitVec.ofNat 64 a)).bitPattern = some a := by
    change some (a % 2 ^ 64) = some a
    rw [Nat.mod_eq_of_lt (by omega)]
  have hc : cvtElem .ue8m0 (.bits 8 (BitVec.ofNat 64 a)) = .ok (.fin (ue8m0Rat a)) :=
    cvtElem_ue8m0 hval rfl ha0 ha
  simp only [execCvt, pairCvt, readValue, readReg, hr, FType.layout?, FType.fmt?,
    CvtRnd.mode?, Bind.bind, Except.bind, Pure.pure, Except.pure, Option.bind_some,
    Option.map_some, reduceCtorEq, ↓reduceIte, or_self, false_or, cvtScales]
  simp only [packedElems, bits16] at hw ⊢
  rw [hw]
  simp only [Value.bytes, Nat.reduceDiv, ↓reduceIte, Bind.bind, Except.bind, Pure.pure,
    Except.pure, hc]
  have hw' : widenElem (pairCvt .ue8m0 src dst) .bf16 FloatFmt.bf16.layout false
      (.fin (ue8m0Rat a)) = .ok (.fin (ue8m0Rat a)) := by
    rw [widenElem_fin (ue8m0_rat_bound ha)]
    rfl
  change (do
    let lo ← widenElem (pairCvt .ue8m0 src dst) .bf16 FloatFmt.bf16.layout false (.fin (ue8m0Rat a))
    let hi ← widenElem (pairCvt .ue8m0 src dst) .bf16 FloatFmt.bf16.layout false (.fin (ue8m0Rat a))
    let v ← cvtPack .bf16 FloatFmt.bf16.layout lo hi
    pure (next (setReg t dst v)) : Exec TState) = _
  simp [hw', bind, Except.bind, pure, Except.pure, cvtPack, FType.fmt?, FVal.toValue,
    ue8m0_rat_real, Assumptions.bf16Pair]


theorem execLocalA_dequant {op : Op} (hsite : 2696 ≤ t.pc)
    (hi : idealArith.localRule L g t op = none) (ha : approx.localRule L g t op = none)
    (hc : cvtBf16x2.localRule L g t op = none) (hl : lg2Exact.localRule L g t op = none) :
    execLocalA all L g t op =
      (mulBf16x2.localRule L g t op).getD
        ((cvtUe8m0.localRule L g t op).getD (execLocal L g t op)) := by
  have hp : t.pc ∉ paramAdds := by
    simp [paramAdds]
    omega
  have hf : t.pc ∉ prefetchTensorMapSites := by
    simp [prefetchTensorMapSites]
    omega
  have hs : t.pc ∉ sharedBitsSites := by
    simp [sharedBitsSites]
    omega
  have hd : deadPackRule L g t op = none :=
    deadPackRule_of_none (deadPackWords.eq_3 _ (by omega) (by omega))
  have hpeer : peerPackRule t op = none :=
    peerPackRule_of_none (peerPack_none_of_outside (Or.inr (by omega)))
  have hpar : paramPointers.localRule L g t op = none := by simp [paramPointers, hp, hf]
  have hsh : sharedBits.localRule L g t op = none := by simp [sharedBits, hs, hd, hpeer]
  have hnc : ncReadOnly.localRule L g t op = none := rfl
  have hdr : storeDrain.localRule L g t op = none := rfl
  have hco : commitOrder.localRule L g t op = none := rfl
  have hn : ∀ a ∈ all, a.segmentRule L g t = none := by
    simp [all, idealArith, approx, Assumption.idealReal, Assumption.approxExact, mulBf16x2,
      cvtBf16x2, cvtUe8m0, lg2Exact, ncReadOnly, Assumption.ncReadOnly, paramPointers,
      storeDrain, sharedBits, commitOrder, Assumption.commitOrderAt]
  rw [execLocalA_noSegment hn, execLocalRule]
  simp only [all, List.findSome?_cons, List.findSome?_nil, hi, ha, hc, hl, hpar, hsh, hnc, hdr,
    hco]
  cases mulBf16x2.localRule L g t op <;> cases cvtUe8m0.localRule L g t op <;> rfl

theorem execLocalA_e4m3 {src dst a b : Nat} (hsite : 2696 ≤ t.pc)
    (hr : t.regs src = some (bits16 (a + 256 * b))) (ha : a < 256) (hb : b < 256) (ha1 : a ≠ 127)
    (ha2 : a ≠ 255) (hb1 : b ≠ 127) (hb2 : b ≠ 255) :
    execLocalA all L g t (.cvt (pairCvt .e4m3 src dst)) =
      .ok (next (setReg t dst (.pair (e4m3Widened a) (e4m3Widened b)))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  change execCvt L g t (pairCvt .e4m3 src dst) = _
  exact e4m3_execCvt hr ha hb ha1 ha2 hb1 hb2

theorem execLocalA_ue8m0 {src dst a : Nat} (hsite : 2696 ≤ t.pc)
    (hr : t.regs src = some (bits16 (a + 256 * a))) (ha : a < 255) :
    execLocalA all L g t (.cvt (pairCvt .ue8m0 src dst)) =
      .ok (next (setReg t dst (bf16Pair (ue8m0Val a) (ue8m0Val a)))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  by_cases hz : a = 0
  · subst a
    simp [mulBf16x2, cvtUe8m0, pairCvt, readBits, readReg, hr, bits16,
      truncBits, pure, Except.pure, bind, Except.bind]
  · have hbits : readBits L g t 16 (.reg src) = .ok (BitVec.ofNat 64 (a + 256 * a)) := by
      have hb : a + 256 * a < 65536 := by omega
      simp [readBits, readReg, hr, bits16, truncBits, Nat.mod_eq_of_lt hb,
        bind, Except.bind, pure, Except.pure]
    have hw : (BitVec.ofNat 64 (a + 256 * a)).toNat = a + 256 * a := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlo : (a + 256 * a) % 256 = a := by omega
    have hhi : (a + 256 * a) / 256 % 256 = a := by omega
    simp [mulBf16x2, cvtUe8m0, pairCvt, hbits, hw, hlo, hhi, hz, pure, Except.pure]
    change execCvt L g t (pairCvt .ue8m0 src dst) = _
    exact ue8m0_execCvt_pos hr (by omega) ha

def pairMul (a b dst : Nat) : FloatInstr where
  op := .mul
  ty := ⟨.bf16, 2⟩
  dsts := [some dst]
  srcs := [.reg a, .reg b]

theorem execLocalA_pairMul {a b dst x y scale : Nat} (hsite : 2696 ≤ t.pc)
    (ha : t.regs a = some (.pair (e4m3Widened x) (e4m3Widened y)))
    (hb : t.regs b = some (bf16Pair (ue8m0Val scale) (ue8m0Val scale))) :
    execLocalA all L g t (.float (pairMul a b dst)) =
      .ok (next (setReg t dst (bf16Pair (e4m3Val x * ue8m0Val scale)
        (e4m3Val y * ue8m0Val scale)))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  simp [pairMul, mulBf16x2, pairValue, readValue, readReg, ha, hb, bf16Pair, e4m3Widened_real,
    valFloat_float, Except.toOption, pure, Except.pure]

/-- A byte of one of the integer words supplied by the shared loads, little-endian. -/
def byteAt (word i : Nat) : Nat := word / 256 ^ i % 256

theorem byteAt_lt (word i : Nat) : byteAt word i < 256 := Nat.mod_lt _ (by decide)

theorem rawPairBits_eq (word j : Nat) :
    word / 2 ^ (16 * j) % 2 ^ 16 =
      byteAt word (2 * j) + 256 * byteAt word (2 * j + 1) := by
  have hp : 256 ^ (2 * j) = 2 ^ (16 * j) := by
    rw [show (256 : Nat) = 2 ^ 8 by decide, ← pow_mul]
    congr 1
    omega
  simp only [byteAt, pow_succ, ← Nat.div_div_eq_div_mul, hp]
  generalize word / 2 ^ (16 * j) = n
  omega


/-- The two consecutive bf16 values computed by one packed multiply. -/
def dequantPair (word scale pair : Nat) : Value :=
  bf16Pair (e4m3Val (byteAt word (2 * pair)) * ue8m0Val scale)
    (e4m3Val (byteAt word (2 * pair + 1)) * ue8m0Val scale)

/-- The eight bf16 values that one lane packs into its 128-bit shared store. -/
def dequantChunk (word scale : Nat) : Value :=
  .pair (.pair (dequantPair word scale 0) (dequantPair word scale 1))
    (.pair (dequantPair word scale 2) (dequantPair word scale 3))

theorem dequantChunk_width (word scale : Nat) : (dequantChunk word scale).bytes = 16 := rfl

theorem dequantChunk_toBytes (word scale : Nat) :
    (dequantChunk word scale).toBytes = (List.range 8).flatMap fun i =>
      (Value.float .bf16 (e4m3Val (byteAt word i) * ue8m0Val scale)).toBytes := rfl

/-- Register index within the sixteen unpacked scale bytes of a row. -/
def scaleByteRegIndex (i : Nat) : Nat := 4 * (3 - i / 4) + (i + 2) % 4

theorem scaleByteRegIndex_lt (i : Nat) : scaleByteRegIndex i < 16 := by
  unfold scaleByteRegIndex
  omega

/-- The word reversal and intra-word permutation preserve the logical byte at index `i`. -/
theorem scaleRegByte_eq (sc : Nat) (i : Fin 16) :
    let j := scaleByteRegIndex i.val
    sc / 256 ^ (4 * (3 - j / 4)) % 256 ^ 4 / 256 ^ ((j + 2) % 4) % 256 =
      byteAt sc i.val := by
  fin_cases i <;> norm_num [scaleByteRegIndex, byteAt] <;> omega

/-- The integer multiply on a scale byte broadcasts it into the two packed halves. -/
def dupScale (src dst : Nat) : IntInstr :=
  ⟨.mul .lo, .int .s 16, false, [some dst], [.reg src, .imm 257]⟩

theorem execLocalA_dupScale {src dst a : Nat} (hsite : 2696 ≤ t.pc)
    (hr : t.regs src = some (bits16 a)) (ha : a < 256) :
    execLocalA all L g t (.int (dupScale src dst)) =
      .ok (next (setReg t dst (bits16 (a + 256 * a)))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  change execInt L g t (dupScale src dst) = _
  simp only [execInt, dupScale, DType.width, readBits, readReg, hr, bits16, bind, Except.bind,
    pure, Except.pure]
  congr 4
  apply BitVec.eq_of_toNat_eq
  rw [show BitVec.ofInt 64 257 = BitVec.ofNat 64 257 from rfl]
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_mul, Nat.reducePow,
    Nat.reduceMod]
  have ha16 : a < 65536 := by omega
  have ha64 : a < 18446744073709551616 := by omega
  have hm16 : a * 257 < 65536 := by omega
  have hm64 : a * 257 < 18446744073709551616 := by omega
  have hsum : a + 256 * a < 18446744073709551616 := by omega
  simp only [Nat.mod_eq_of_lt ha16, Nat.mod_eq_of_lt ha64,
    Nat.mod_eq_of_lt hm16, Nat.mod_eq_of_lt hm64, Nat.mod_eq_of_lt hsum]
  omega

def selScale (p a b dst : Nat) : IntInstr :=
  ⟨.selp, .int .b 16, false, [some dst], [.reg a, .reg b, .reg p]⟩

theorem execLocalA_selScale {p a b dst hi lo : Nat} {pick : Bool} (hsite : 2696 ≤ t.pc)
    (hp : t.regs p = some (.pred pick)) (ha : t.regs a = some (bits16 hi))
    (hb : t.regs b = some (bits16 lo)) :
    execLocalA all L g t (.int (selScale p a b dst)) =
      .ok (next (setReg t dst (bits16 (if pick then hi else lo)))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  change execMove L g t (.int (selScale p a b dst)) = _
  cases pick <;>
    simp [execMove, selScale, readValue, readReg, hp, ha, hb, bits16, DType.width,
      Value.bytes, bind, Except.bind, pure, Except.pure]

def packChunk (w a b dst : Nat) : MoveInstr :=
  ⟨.pack, .int .b w, [some dst], [.reg a, .reg b]⟩

theorem execLocalA_packChunk {w a b dst : Nat} {lo hi : Value} (hsite : 2696 ≤ t.pc)
    (hw : w = 64 ∨ w = 128) (ha : t.regs a = some lo) (hb : t.regs b = some hi)
    (hlo : lo.bytes = w / 16) (hhi : hi.bytes = w / 16) :
    execLocalA all L g t (.move (packChunk w a b dst)) =
      .ok (next (setReg t dst (joinValue lo hi))) := by
  rw [execLocalA_dequant hsite rfl rfl rfl rfl]
  have hmove : execLocal L g t (.move (packChunk w a b dst)) =
      execMove L g t (.move (packChunk w a b dst)) := by
    rcases hw with rfl | rfl <;> rfl
  change execLocal L g t (.move (packChunk w a b dst)) = _
  rw [hmove]
  simp [execMove, packChunk, readValue, readReg, ha, hb, DType.width, hlo, hhi,
    bind, Except.bind, pure, Except.pure]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2.Numeric
