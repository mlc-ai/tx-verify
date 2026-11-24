-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Flow.Widen

@[expose] public section

/-! # Floating reads of a word whose number a hypothesis gives

A proof tool. A launch word that holds a binary32 pattern (a scale passed as bits, say) sits in a
register as `.bits 32 x` with a symbolic `x`; Core reads it as a float through its pattern
(`classify`), which does not evaluate on a symbolic pattern. A kernel's `Pre` gives the pattern's
number (`f32Value n = some s`), from which the word classifies as the finite datum `s`
(`classify_word_f32`, `classify_word` for a launch word `truncBits 32 n`). From a hypothesis
`classify .f32 (.bits 32 x) = .ok (.fin s)`:

* the word reads as `s` for Core's rules (`bitsAsFloat_word_f32`) and the assumptions' rules
  (`readEReal_bits_fin`); a `neg.f32` or `abs.f32` of it writes `-s` or `|s|`
  (`execLocal_negWord`, `execLocal_absWord`);
* a pack `mov.b64 d, {a, b}` of two such words (Core joins two words into one 64-bit word,
  `joinValue`) reads as the pair of their numbers when the low word fits its 32 bits
  (`pairRead_bits_or`, `pairRead_join_bits`): `classify .f32` reads only the low 32 bits of a
  word (`classify_bits32_mod`), and the halves of the joined word are the two words' low bits.

`seg_sym` uses these when such a hypothesis is in context (`Seg.negWord`, `Seg.absWord`, and the
operand reads of `ruleStepProof`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- **A word whose binary32 number is `s ≠ 0` classifies as the finite datum `s`.** -/
theorem classify_word_f32 {x : BitVec 64} {s : ℚ} (hx : f32Value x.toNat = some s)
    (hs : s ≠ 0) : classify .f32 (.bits 32 x) = .ok (.fin s) := by
  simp only [f32Value, FloatFmt.decode, Option.bind_eq_some_iff] at hx
  obtain ⟨v, hv, hn⟩ := hx
  have hb : (Value.bits 32 x).bytes = FloatFmt.f32.bytes := rfl
  cases v with
  | zero _ => simp only [FVal.num, Option.some.injEq] at hn; exact absurd hn.symm hs
  | fin q =>
    simp only [FVal.num, Option.some.injEq] at hn
    subst hn
    simp [classify, Value.bitPattern, hb, hv, pure, Except.pure]
  | inf _ => simp [FVal.num] at hn
  | nan _ => simp [FVal.num] at hn

/-- A word whose binary32 number is `s ≠ 0` reads as the real `s`. -/
theorem bitsAsFloat_word_f32 {x : BitVec 64} {s : ℚ} (hx : f32Value x.toNat = some s)
    (hs : s ≠ 0) : bitsAsFloat .f32 (.bits 32 x) = .ok (s : ℝ) := by
  simp [bitsAsFloat, classify_word_f32 hx hs, FVal.finite, bind, Except.bind, pure, Except.pure]

/-- **A launch word** `truncBits 32 n` whose binary32 number is `s ≠ 0` classifies as `s`. -/
theorem classify_word {S : Nat} {s : ℚ} (hS : f32Value S = some s) (h0 : s ≠ 0)
    (h32 : S < 2 ^ 32) :
    classify .f32 (.bits 32 (truncBits 32 (BitVec.ofNat 64 S))) = .ok (FVal.fin s) := by
  refine classify_word_f32 ?_ h0
  have : (truncBits 32 (BitVec.ofNat 64 S)).toNat = S := by
    simp only [truncBits, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : S < 2 ^ 64), Nat.mod_eq_of_lt h32,
      Nat.mod_eq_of_lt (by omega : S < 2 ^ 64)]
  rw [this]; exact hS

/-- `classify .f32` of a 32-bit word reads only its low 32 bits. -/
theorem classify_bits32_mod {x y : BitVec 64} (h : x.toNat % 2 ^ 32 = y.toNat % 2 ^ 32) :
    classify .f32 (.bits 32 x) = classify .f32 (.bits 32 y) := by
  have hd : ∀ n, FloatFmt.f32.layout.decode n = FloatFmt.f32.layout.decode (n % 2 ^ 32) := by
    intro n
    have hw : (Layout.binary 8 23 true Specials.ieee).width = 32 := rfl
    simp only [FloatFmt.layout, Layout.decode, hw, Nat.mod_mod]
  simp only [classify, Value.bitPattern]
  rw [hd x.toNat, hd y.toNat, h]
  rfl

/-- A word that classifies as the finite datum `s` reads as `s` in the extended reals (the
reading of the assumptions' rules). -/
theorem readEReal_bits_fin {w : Nat} {x : BitVec 64} {s : ℚ}
    (h : classify .f32 (.bits w x) = .ok (.fin s)) :
    Assumption.readEReal .f32 (.bits w x) = some (.ok ((s : ℝ) : EReal)) := by
  simp [Assumption.readEReal, h, Assumption.readEReal.ofDatum, pure, Except.pure]

theorem truncBits32_toNat (x : BitVec 64) : (truncBits 32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem truncBits_toNat_lt (w : Nat) (x : BitVec 64) : (truncBits w x).toNat < 2 ^ w := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by positivity))

theorem toNat_or_shl32_lo {a b : BitVec 64} :
    (a ||| b <<< 32).toNat % 2 ^ 32 = a.toNat % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 32 <;> simp [hi]

theorem toNat_or_shl32_hi {a b : BitVec 64} (ha : a.toNat < 2 ^ 32) :
    (a ||| b <<< 32).toNat / 2 ^ 32 % 2 ^ 32 = b.toNat % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, BitVec.testBit_toNat,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  by_cases hi : i < 32
  · have : a.getLsbD (i + 32) = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]; omega
  · simp [hi]

/-- **The pair read of two joined words** (`mov.b64 d, {a, b}` of two 32-bit words, which Core
joins into `a ||| b <<< 32`): the reads of the two words, when the low word fits its 32 bits. -/
theorem pairRead_bits_or {a b : BitVec 64} {x y : EReal} (ha32 : a.toNat < 2 ^ 32)
    (ha : Assumption.readEReal .f32 (.bits 32 a) = some (.ok x))
    (hb : Assumption.readEReal .f32 (.bits 32 b) = some (.ok y)) :
    pairRead (.bits 64 (a ||| b <<< 32)) = some (.ok (x, y)) := by
  have hl : Assumption.readEReal .f32 (.bits 32 (truncBits 32 (a ||| b <<< 32))) =
      some (.ok x) := by
    rw [← ha]; simp only [Assumption.readEReal]
    rw [classify_bits32_mod (y := a) (by rw [truncBits32_toNat, Nat.mod_mod, toNat_or_shl32_lo])]
  have hh : Assumption.readEReal .f32
      (.bits 32 (truncBits 32 (BitVec.ofNat 64 ((a ||| b <<< 32).toNat / 2 ^ 32)))) =
      some (.ok y) := by
    rw [← hb]; simp only [Assumption.readEReal]
    rw [classify_bits32_mod (y := b) (by
      rw [truncBits32_toNat, Nat.mod_mod, BitVec.toNat_ofNat,
        Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64)]
      exact toNat_or_shl32_hi ha32)]
  simp only [pairRead, splitValue]
  rw [hl, hh]; rfl

/-- The pair read of the join of two words (`pairRead_bits_or` before the join is evaluated). -/
theorem pairRead_join_bits {a b : BitVec 64} {x y : EReal} (ha32 : a.toNat < 2 ^ 32)
    (ha : Assumption.readEReal .f32 (.bits 32 a) = some (.ok x))
    (hb : Assumption.readEReal .f32 (.bits 32 b) = some (.ok y)) :
    pairRead (joinValue (.bits 32 a) (.bits 32 b)) = some (.ok (x, y)) := by
  simpa [joinValue] using pairRead_bits_or ha32 ha hb

/-- `neg.f32 d, r` (no `.ftz`) on a register holding a word that classifies as the finite datum
`s`: Core writes the payload `-s`. -/
theorem execLocal_negWord {L : Launch} {g : Nat} {t : TState} {d r : Nat} {x : BitVec 64}
    {s : ℚ} (hr : t.regs r = some (.bits 32 x)) (hx : classify .f32 (.bits 32 x) = .ok (.fin s)) :
    execLocal L g t (.float { op := .neg, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }) =
      .ok (PTX.next (setReg t d (.float .f32 ((-s : ℚ) : ℝ)))) := by
  simp [execLocal, Op.rule, FloatInstr.rule, execFloat, boolCombine, readValue, readReg, hr,
    floatLane, hx, FloatInstr.lane, FloatInstr.ieee, FloatInstr.flushIn,
    FVal.negate, FVal.toValue, bind, Except.bind, pure, Except.pure]

/-- `abs.f32 d, r` (no `.ftz`) on a register holding a word that classifies as the finite datum
`s`: Core writes the payload `|s|`. -/
theorem execLocal_absWord {L : Launch} {g : Nat} {t : TState} {d r : Nat} {x : BitVec 64}
    {s : ℚ} (hr : t.regs r = some (.bits 32 x)) (hx : classify .f32 (.bits 32 x) = .ok (.fin s)) :
    execLocal L g t (.float { op := .abs, ty := ⟨.f32, 1⟩, dsts := [some d], srcs := [.reg r] }) =
      .ok (PTX.next (setReg t d (.float .f32 ((|s| : ℚ) : ℝ)))) := by
  simp [execLocal, Op.rule, FloatInstr.rule, execFloat, boolCombine, readValue, readReg, hr,
    floatLane, hx, FloatInstr.lane, FloatInstr.ieee, FloatInstr.flushIn,
    FVal.isNaN, FVal.absV, FVal.toValue, bind, Except.bind, pure, Except.pure]

end

end PTX.Flow
