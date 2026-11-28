-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatJ
public import Lemmas.Flow.OutFloatItems
public import Lemmas.Flow.Lg2Core

@[expose] public section

/-! # `neg.f32` and `lg2.approx.ftz.f32` on `.f32` data

`negE_total`: the outcome of `neg{.ftz}.f32` (`OutFloatItems.lean`) of a datum of four bytes is a
datum of four bytes, the ideal negation or Core's rule on a NaN. For `lg2.approx.ftz.f32` the
exact rule covers a positive finite operand and Core's table every other class a datum can have:
`lg2_nonpos` shows that a datum the exact rule declines is not a positive number (a payload
`.float .f32 y` with `y < 0` classifies by the pattern `2^31 + F`, `classify_f32_neg`), and
`lg2I_lane` that the table has a row for it. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Assumption
noncomputable section

theorem encode_f32_neg {y : ℝ} (hy : y < 0) :
    ∃ F, F ≤ FloatFmt.f32.maxField ∧ FloatFmt.f32.encode y = 2 ^ 31 + F := by
  rw [FloatFmt.encode_eq]
  have e : FloatFmt.f32.expBits + FloatFmt.f32.mantBits = 31 := rfl
  simp only [e, hy, ite_true]
  have hle := Nat.findGreatest_le (P := fun F => (FloatFmt.f32.magnitude F : ℝ) ≤ |y|)
    FloatFmt.f32.maxField
  split_ifs with h
  · exact ⟨_, h.1, rfl⟩
  · exact ⟨_, hle, rfl⟩

theorem decode_f32_neg {F : Nat} (hF : F < 2 ^ 31) :
    ∃ c, FloatFmt.f32.layout.decode (2 ^ 31 + F) = some c ∧ ∀ q, c = .fin q → q < 0 := by
  have h1 : (2147483648 + F) % 4294967296 = 2147483648 + F := Nat.mod_eq_of_lt (by omega)
  have h2 : (2147483648 + F) % 2147483648 = F := by omega
  have h3 : (2147483648 + F) / 2147483648 % 2 = 1 := by omega
  simp only [FloatFmt.layout, Layout.decode, Layout.width, ite_true, Nat.reduceAdd, Nat.reducePow,
    h1, h2, h3, Bool.true_and, beq_self_eq_true]
  split_ifs with ha hb
  · exact ⟨_, rfl, nofun⟩
  · exact ⟨_, rfl, nofun⟩
  · refine ⟨_, rfl, fun q hq => ?_⟩
    by_cases hz : F = 0
    · simp [Layout.fieldVal, hz] at hq
    · simp only [Layout.fieldVal, hz, ↓reduceIte, FVal.fin.injEq] at hq
      have hp : (0 : ℚ) < Layout.magnitude 8 23 F := by
        have := Layout.magnitude_strictMono 8 23 (Nat.pos_of_ne_zero hz)
        simpa [Layout.magnitude_zero] using this
      rw [← hq]
      linarith

theorem classify_f32_neg {y : ℝ} (hy : y < 0) :
    ∃ c, classify .f32 (.float .f32 y) = .ok c ∧ ∀ q, c = .fin q → q < 0 := by
  obtain ⟨F, hF, hn⟩ := encode_f32_neg hy
  obtain ⟨c, hc, hq⟩ := decode_f32_neg (F := F) (lt_of_le_of_lt hF (by decide))
  have hc' : FloatFmt.f32.layout.decode (2147483648 + F) = some c := by simpa using hc
  refine ⟨c, ?_, hq⟩
  simp [classify, Value.bitPattern, hn, Value.bytes, hc', pure, Except.pure]

theorem magnitude_pos {F : Nat} (hz : F ≠ 0) : (0 : ℚ) < Layout.magnitude 8 23 F := by
  have := Layout.magnitude_strictMono 8 23 (Nat.pos_of_ne_zero hz)
  simpa [Layout.magnitude_zero] using this

theorem decode_f32_fin_ne {n : Nat} {q : ℚ} (h : FloatFmt.f32.layout.decode n = some (.fin q)) :
    q ≠ 0 := by
  simp only [FloatFmt.layout, Layout.decode, Layout.width, ite_true, Nat.reduceAdd,
    Nat.reducePow, Layout.fieldVal] at h
  split_ifs at h with h1 h2 h3 h4
  · cases h
  · cases h
  · cases h
  · simp only [Option.some.injEq, FVal.fin.injEq] at h
    have := magnitude_pos h3
    subst h
    linarith
  · simp only [Option.some.injEq, FVal.fin.injEq] at h
    have := magnitude_pos h3
    subst h
    exact this.ne'

theorem classify_fin_ne {v : Value} {q : ℚ} (h : classify .f32 v = .ok (.fin q)) : q ≠ 0 := by
  cases v with
  | nan f =>
    simp only [classify] at h
    split_ifs at h
    all_goals cases h
  | _ =>
    simp only [classify] at h
    split at h
    · split_ifs at h
      · split at h
        · rename_i hd
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact decode_f32_fin_ne hd
        · cases h
    · cases h

theorem lg2_nonpos {va : Value} {c : FVal} {x : EReal} (hc : classify .f32 va = .ok c)
    (hx : readEReal .f32 va = some (.ok x)) (h0 : ¬(0 < x ∧ x ≠ ⊤)) :
    ∀ q, c = .fin q → q < 0 := by
  intro q hq
  subst hq
  have hne := classify_fin_ne hc
  by_cases hf : ∃ y, va = .float .f32 y
  · obtain ⟨y, rfl⟩ := hf
    simp only [readEReal, ↓reduceIte, pure, Except.pure, Option.some.injEq, Except.ok.injEq] at hx
    subst hx
    rcases lt_trichotomy y 0 with hl | hz | hg
    · obtain ⟨c', hc', hq'⟩ := classify_f32_neg hl
      rw [hc'] at hc
      cases hc
      exact hq' q rfl
    · subst hz
      rw [classify_f32_zero] at hc
      cases hc
    · exact absurd ⟨by exact_mod_cast hg, EReal.coe_ne_top _⟩ h0
  · have hr : readEReal .f32 va = readEReal.ofDatum (classify .f32 va) := by
      cases va with
      | float f y =>
        by_cases hf' : f = .f32
        · exact absurd ⟨y, by rw [hf']⟩ hf
        · simp [readEReal, hf']
      | _ => simp [readEReal]
    rw [hr, hc] at hx
    simp only [readEReal.ofDatum, pure, Except.pure, Option.some.injEq, Except.ok.injEq] at hx
    subst hx
    by_contra hqn
    exact h0 ⟨by
      have : (0 : ℚ) < q := lt_of_le_of_ne (not_lt.mp hqn) (Ne.symm hne)
      exact_mod_cast this, EReal.coe_ne_top _⟩

theorem readEReal_none_nan {va : Value} {c : FVal} (hc : classify .f32 va = .ok c)
    (h : readEReal .f32 va = none) : ∃ b, c = .nan b := by
  have hd : readEReal.ofDatum (classify .f32 va) = none := by
    cases va with
    | float f y =>
      by_cases hf : f = .f32
      · subst hf; simp [readEReal, pure, Except.pure] at h
      · simpa [readEReal, hf] using h
    | _ => simpa [readEReal] using h
  rw [hc] at hd
  cases c <;> simp [readEReal.ofDatum, pure, Except.pure] at hd ⊢

theorem negI_nan (fz : Bool) (b : Option Nat) :
    ∃ o, FloatInstr.lane (negI fz) [.nan b] = some (.val o) := by
  cases fz <;> exact ⟨_, rfl⟩

/-- **`neg{.ftz}.f32` of an `.f32` datum** is a datum of four bytes. -/
theorem negE_total {fz : Bool} {va : Value} (ha : Dat32 va) :
    ∃ v, negE fz va = .ok v ∧ Dat32 v := by
  obtain ⟨c, hc⟩ := ha.1
  unfold negE idealNeg
  rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
  · obtain ⟨b, rfl⟩ := readEReal_none_nan hc hx
    obtain ⟨o, ho⟩ := negI_nan fz b
    refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
    simp [hx, bindRead, coreFloat, negI, ty1, floatLane, show List.range 1 = [0] from rfl, hc, ho,
      bind, Except.bind, pure, Except.pure]
  · simp only [hx, bindRead, pure, Except.pure]
    exact ⟨_, rfl, dat32_erealValue _⟩

theorem lg2I_lane (c : FVal) (h : ∀ q, c = .fin q → q < 0) :
    ∃ o, FloatInstr.lane (lg2I true) [c] = some (.val o) := by
  cases c with
  | zero n => cases n <;> exact ⟨_, rfl⟩
  | inf n => cases n <;> exact ⟨_, rfl⟩
  | nan b => exact ⟨_, rfl⟩
  | fin q =>
    have hq := h q rfl
    by_cases hs : FloatFmt.f32.layout.subnormal q = true
    · simp [FloatInstr.lane, FloatInstr.approx, FloatInstr.flushIn, FloatInstr.approxTable?,
        FloatInstr.rule, FloatInstr.srcFmt, Layout.flush, lg2Table, ACls.of, hs, hq]
      exact ⟨_, rfl⟩
    · simp [FloatInstr.lane, FloatInstr.approx, FloatInstr.flushIn, FloatInstr.approxTable?,
        FloatInstr.rule, FloatInstr.srcFmt, Layout.flush, lg2Table, ACls.of, hs, hq]
      exact ⟨_, rfl⟩
end
end PTX.Flow.TyG
