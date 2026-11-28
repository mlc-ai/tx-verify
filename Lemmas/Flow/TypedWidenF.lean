-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatF
public import Lemmas.Flow.FloatRead

@[expose] public section

/-! # `cvt.f32.bf16` of a 16-bit pattern

`cvt.f32.bf16 d, a` of a register that holds a pattern of 16 bits has an outcome: a number, a
zero or an infinity widens exactly (the ideal rule of a kernel assumption that reads the form as
exact), and a NaN, which that rule declines, takes the Core rule, which also has a result: every
pattern decodes, and a number of `.bf16` is within MAX_NORM of `.f32`. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

theorem maxNorm_bf16_le : FloatFmt.bf16.layout.maxNorm ≤ FloatFmt.f32.layout.maxNorm := by
  decide +kernel

theorem bf16_width : (Layout.binary 8 7 true .ieee).width = 16 := rfl

theorem decode_bf16 (n : Nat) : ∃ c, FloatFmt.bf16.layout.decode n = some c := by
  simp only [FloatFmt.layout, Layout.decode, bf16_width]
  norm_num
  by_cases hE : n % 32768 / 128 = 255
  · by_cases hm : n % 128 = 0 <;> simp [hE, hm]
  · simp [hE]

/-- A number a `.bf16` pattern decodes to is within MAX_NORM of `.f32`. -/
theorem bf16_fin_bound {n : Nat} {q : ℚ} (h : FloatFmt.bf16.layout.decode n = some (.fin q)) :
    |q| ≤ FloatFmt.f32.layout.maxNorm := by
  refine le_trans ?_ maxNorm_bf16_le
  simp only [FloatFmt.layout, Layout.decode, bf16_width] at h
  norm_num at h
  by_cases hE : n % 32768 / 128 = 255
  · by_cases hm : n % 128 = 0 <;> simp [hE, hm] at h
  · simp only [hE, ite_false, Option.some.injEq] at h
    unfold Layout.fieldVal at h
    by_cases hF : n % 32768 = 0
    · simp [hF] at h
    · simp only [hF, ite_false, FVal.fin.injEq] at h
      have hmono : Layout.magnitude 8 7 (n % 32768) ≤ FloatFmt.bf16.layout.maxNorm :=
        (Layout.magnitude_strictMono 8 7).monotone (by
          simp only [FloatFmt.layout, Layout.topField]; omega)
      have hnn := Layout.magnitude_nonneg 8 7 (n % 32768)
      rw [← h]
      split_ifs <;> simp [abs_neg, abs_of_nonneg hnn, hmono]

/-- `cvt.f32.bf16 d, a`. -/
abbrev widenBfC (d : Nat) (a : Opnd) : CvtInstr :=
  { dst := .float .f32, src := .float .bf16, d := d, srcs := [a] }

theorem classify_bf16_bits (x : BitVec 64) :
    ∃ c, classify .bf16 (.bits 16 x) = .ok c ∧ FloatFmt.bf16.layout.decode x.toNat = some c := by
  obtain ⟨c, hc⟩ := decode_bf16 x.toNat
  exact ⟨c, by simp [classify, Value.bitPattern, Value.bytes, FloatFmt.bytes, hc, pure,
    Except.pure], hc⟩

/-- A datum of `.bf16` widens exactly to `.f32`. -/
theorem widenElem_bf16 {n : Nat} {x : FVal} (h : FloatFmt.bf16.layout.decode n = some x) :
    ∃ y, widenElem (widenBfC 0 (.reg 0)) .f32 FloatFmt.f32.layout false x = .ok y := by
  cases x with
  | zero neg => exact ⟨.zero neg, by simp [widenElem, cvtSpecial, cvtFinish, FloatFmt.layout,
      bind, Except.bind, pure, Except.pure]⟩
  | inf neg => exact ⟨.inf neg, by simp [widenElem, cvtSpecial, cvtFinish, FloatFmt.layout,
      bind, Except.bind, pure, Except.pure]⟩
  | nan p => exact ⟨.nan none, by simp [widenElem, cvtSpecial, cvtFinish, FloatFmt.layout,
      bind, Except.bind, pure, Except.pure]⟩
  | fin q =>
    have hq := bf16_fin_bound h
    exact ⟨.fin q, by rw [widenElem_fin hq]; simp [cvtFinish, bind, Except.bind, pure, Except.pure]⟩

variable {L : Launch} {g : Nat}

/-- **The Core rule of `cvt.f32.bf16` has a result on every 16-bit pattern**, a datum. -/
theorem execLocal_widenBf_core {t : TState} {d r : Nat} {x : BitVec 64}
    (h : t.regs r = some (.bits 16 x)) :
    ∃ v, execLocal L g t (.cvt (widenBfC d (.reg r))) = .ok (next (setReg t d v)) ∧ Dat32 v := by
  obtain ⟨c, hc, hdec⟩ := classify_bf16_bits x
  obtain ⟨y, hy⟩ := widenElem_bf16 hdec
  have hw : widenElem (widenBfC d (.reg r)) = widenElem (widenBfC 0 (.reg 0)) := rfl
  have hr : (Op.cvt (widenBfC d (.reg r))).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact, CvtInstr.widens]
  refine ⟨y.toValue .f32, ?_, dat32_toValue y⟩
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat_reg (wide := false) h (show (Value.bits 16 x).bytes =
    FloatFmt.bf16.bytes from rfl), FType.fmt?, hw, hc, hy, bind, Except.bind, pure, Except.pure]

theorem readEReal_bf16 (x : BitVec 64) :
    readEReal .bf16 (.bits 16 x) = none ∨ ∃ r, readEReal .bf16 (.bits 16 x) = some (.ok r) := by
  obtain ⟨c, hc, -⟩ := classify_bf16_bits x
  simp only [readEReal, hc]
  rcases c with neg | q | neg | p <;> simp [readEReal.ofDatum, pure, Except.pure]

/-- The ideal reading of `cvt.f32.bf16 d, a` (a kernel's assumption names the form). -/
def execWidenBf (t : TState) (d : Nat) (a : Opnd) : Option (Exec TState) :=
  bindRead (readERealOpnd t .bf16 a) fun x =>
    some (pure (next (setReg t d (erealValue .f32 x))))

/-- At every pc of `[a, b)` the assumptions read `cvt.f32.bf16` of a register as its ideal
reading where that applies, and leave the others to the Core rule. -/
def WidenRules (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b → ∀ d r,
    (∀ e, execWidenBf t d (.reg r) = some e →
      execLocalA A L g t (.cvt (widenBfC d (.reg r))) = e) ∧
    (execWidenBf t d (.reg r) = none →
      execLocalA A L g t (.cvt (widenBfC d (.reg r))) =
        execLocal L g t (.cvt (widenBfC d (.reg r))))

/-- `cvt.f32.bf16 d, a` of a register of 16 bits. -/
def absWiden (env : EnvF) : Op → Option (List (Nat × TagF))
  | .cvt c =>
    match c.srcs with
    | [.reg r] =>
      if decide (c = widenBfC c.d (.reg r)) && env.lookup r == some (.old (.bits 16)) then
        some [(c.d, .dat32)] else none
    | _ => none
  | _ => none

variable {A : List Assumption}

theorem absWiden_sound {a b : Nat} (hR : WidenRules A L g a b) :
    AbsSound A L g a b absWiden := by
  intro env op outs t h ha hb ht
  cases op <;> simp only [absWiden, reduceCtorEq] at h
  rename_i c
  split at h
  · rename_i r _
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    obtain ⟨hf, hl⟩ := hc
    obtain ⟨x, hx⟩ := ht r _ hl
    obtain ⟨hI, hD⟩ := hR t ha hb c.d r
    rw [hf]
    have hrd : readERealOpnd t .bf16 (.reg r) = readEReal .bf16 (.bits 16 x) :=
      readERealOpnd_reg hx
    have hfin : ∃ v, execLocalA A L g t (.cvt (widenBfC c.d (.reg r))) =
        .ok (next (setReg t c.d v)) ∧ Dat32 v := by
      rcases readEReal_bf16 x with e | ⟨q, e⟩
      · obtain ⟨v, hv, hd⟩ := execLocal_widenBf_core (L := L) (g := g) (d := c.d) hx
        refine ⟨v, ?_, hd⟩
        rw [hD (by simp [execWidenBf, hrd, e, bindRead]), hv]
      · refine ⟨erealValue .f32 q, ?_, dat32_erealValue q⟩
        rw [hI (pure (next (setReg t c.d (erealValue .f32 q))))
          (by simp [execWidenBf, hrd, e, bindRead])]
        rfl
    obtain ⟨v, hv, hd⟩ := hfin
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := c.d) (tg := .dat32) ⟨_, rfl, hd⟩
    exact ⟨_, hv, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · simp at h

end
end PTX.Flow.TyG
