-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # A fused multiply-add rounded to nearest has an outcome on every `.f32` datum

A proof tool. `F32Dat v` says that `classify` reads `v` as an `.f32` datum: a number, a zero, an
infinity or a NaN. On three such operands `fma.rn.f32` (no `.ftz`) has an outcome
(`floatE_fma_dat`): where the ideal rule (ASM-IDEAL) applies it is the ideal result, and where it
declines the Core rule (THREAD-FLOAT, IEEE `fma` rounded to nearest) gives the result, which
exists for every datum (`Layout.round` to nearest on `.f32` always has a result:
`round_f32_rn`). The outcome is again an `.f32` datum, and so is every outcome of `add.f32`
(`floatE_add_dat`). So a running value that is updated by such instructions stays a datum
whatever infinities or NaNs reach it. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- `classify` reads `v` as an `.f32` datum. -/
def F32Dat (v : Value) : Prop := ∃ c, classify .f32 v = .ok c

/-- Every 32-bit pattern decodes to an `.f32` datum. -/
theorem decode_f32 (n : Nat) : ∃ c, FloatFmt.f32.layout.decode n = some c := by
  rcases h : FloatFmt.f32.layout.decode n with _ | c
  · have hne : ∀ {α : Type} (p q : Prop) [Decidable p] [Decidable q] (a b c : α),
        (if p then (if q then some a else some b) else some c) ≠ none := by
      intro α p q _ _ a b c
      split_ifs <;> simp
    exact absurd h (hne _ _ _ _ _)
  · exact ⟨c, rfl⟩

theorem f32Dat_of_pattern {v : Value} {n : Nat} (hn : ∀ f, v ≠ .nan f)
    (hp : v.bitPattern = some n) (hb : v.bytes = 4) : F32Dat v := by
  obtain ⟨c, hc⟩ := decode_f32 n
  refine ⟨c, ?_⟩
  have hb' : v.bytes = FloatFmt.f32.bytes := hb
  cases v with
  | nan f => exact absurd rfl (hn f)
  | _ => simp only [classify, hp, hb', ite_true, hc, pure, Except.pure]

theorem f32Dat_bits (x : BitVec 64) : F32Dat (.bits 32 x) :=
  f32Dat_of_pattern (fun _ => by simp) rfl rfl

theorem f32Dat_float (x : ℝ) : F32Dat (.float .f32 x) :=
  f32Dat_of_pattern (fun _ => by simp) rfl rfl

theorem f32Dat_nan : F32Dat (.nan .f32) := ⟨.nan none, rfl⟩

theorem f32Dat_toValue (c : FVal) : F32Dat (c.toValue .f32) := by
  rcases c with neg | q | neg | p
  · cases neg
    · exact f32Dat_float 0
    · exact f32Dat_bits _
  · exact f32Dat_float _
  · exact f32Dat_bits _
  · cases p
    · exact f32Dat_nan
    · exact f32Dat_bits _

theorem f32Dat_erealValue (r : EReal) : F32Dat (erealValue .f32 r) := by
  unfold erealValue
  split_ifs
  · exact f32Dat_toValue _
  · exact f32Dat_toValue _
  · exact f32Dat_float _

/-- A datum's extended-real reading is a number or declines (NaN); it is never a fault. -/
theorem readEReal_dat {v : Value} (h : F32Dat v) :
    readEReal .f32 v = none ∨ ∃ x, readEReal .f32 v = some (.ok x) := by
  obtain ⟨c, hc⟩ := h
  have hd : readEReal.ofDatum (.ok c) = none ∨ ∃ x, readEReal.ofDatum (.ok c) = some (.ok x) := by
    rcases c with neg | q | neg | p <;> simp [readEReal.ofDatum, pure, Except.pure]
  cases v with
  | float f x =>
    by_cases hf : f = .f32
    · subst hf
      exact Or.inr ⟨(x : EReal), by simp [readEReal, pure, Except.pure]⟩
    · simp only [readEReal, hf, ite_false, hc]
      exact hd
  | _ => simp only [readEReal, hc]; exact hd

/-- `Layout.round` to nearest on `.f32` always has a result. -/
theorem round_f32_rn (q : ℝ) (z : Bool) :
    ∃ v, FloatFmt.f32.layout.round .rn .inf q z = some v := by
  simp only [FloatFmt.layout, Layout.round, RoundMode.applies]
  split_ifs <;> first
    | (simp_all; done)
    | (simp only [RoundMode.away]; split_ifs <;> simp)

/-- The Core rule of `fma.rn.f32` has a result on every three data. -/
theorem coreFloat_fma_rn {a b c : Value} (ha : F32Dat a) (hb : F32Dat b) (hc : F32Dat c) :
    ∃ o : FVal, coreFloat (fmaI .rn false) [a, b, c] = .ok (o.toValue .f32) := by
  obtain ⟨xa, hxa⟩ := ha
  obtain ⟨xb, hxb⟩ := hb
  obtain ⟨xc, hxc⟩ := hc
  have hr : ∀ w : FVal, ∃ o, FloatFmt.f32.layout.roundVal .rn false w = some o := by
    intro w
    cases w with
    | fin q =>
      obtain ⟨o, ho⟩ := round_f32_rn (q : ℝ) false
      exact ⟨o, by simp [Layout.roundVal, Layout.roundFtz, ho]⟩
    | _ => exact ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := hr ((xa.mul xb).add .rn xc)
  have hl : FloatInstr.lane (fmaI .rn false) [xa, xb, xc] = some (.val o) := by
    simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.arith,
      FloatInstr.flushIn, FloatRound.mode, ho]
  exact ⟨o, by simp [coreFloat, floatLane, hxa, hxb, hxc, hl, bind, Except.bind, pure,
    Except.pure]⟩

/-- **`fma.rn.f32` on three `.f32` data has an outcome**, and it is an `.f32` datum. -/
theorem floatE_fma_dat {a b c : Value} (ha : F32Dat a) (hb : F32Dat b) (hc : F32Dat c) :
    ∃ v, floatE (fmaI .rn false) [a, b, c] = .ok v ∧ F32Dat v := by
  unfold floatE
  cases hI : idealVal (fmaI .rn false) [a, b, c] with
  | none =>
    obtain ⟨o, ho⟩ := coreFloat_fma_rn ha hb hc
    exact ⟨_, ho, f32Dat_toValue o⟩
  | some r =>
    simp only [idealVal] at hI
    rcases readEReal_dat ha with hx | ⟨x, hx⟩ <;> simp only [bindRead, hx] at hI
    · cases hI
    rcases readEReal_dat hb with hy | ⟨y, hy⟩ <;> simp only [hy] at hI
    · cases hI
    rcases readEReal_dat hc with hz | ⟨z, hz⟩ <;> simp only [hz] at hI
    · cases hI
    rcases hm : mulEReal x y with _ | p <;> simp only [hm, Option.bind_none,
      Option.bind_some, Option.map_none, reduceCtorEq] at hI
    rcases hs : addEReal p z with _ | s <;> simp only [hs, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hI
    exact ⟨_, hI.symm, f32Dat_erealValue s⟩

/-- **Every outcome of `add.f32` is an `.f32` datum.** -/
theorem floatE_add_dat {fz : Bool} {a b v : Value} (hv : floatE (addI fz) [a, b] = .ok v) :
    F32Dat v := by
  unfold floatE at hv
  split at hv
  · rename_i r hr
    subst hv
    simp only [idealVal] at hr
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    obtain ⟨r, rfl⟩ := map_pure_ok hr
    exact f32Dat_erealValue r
  · obtain ⟨e, he⟩ := coreFloat_add_error (fz := fz) a b
    rw [he] at hv
    cases hv

end
end PTX.Flow
