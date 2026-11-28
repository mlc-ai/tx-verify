-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatF
public import Lemmas.Flow.MinCore

@[expose] public section

/-! # `min.f32` and `fma.rn.f32` on `.f32` data

The two instructions of `TypedFloatF.lean`'s kind that it left out: the outcomes `minE` and
`floatE (fmaI .rn false)` are total on `.f32` data (an ideal-real reading, or the Core rule where
that declines) and are again data of four bytes without a slice (`Dat32`). `absFloat2` is the
abstract rule of the two. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption PTX.Flow.MinCore

noncomputable section

theorem minI_lane : ∀ xs : List FVal, 2 ≤ xs.length → ∃ o, FloatInstr.lane minI xs = some (.val o)
  | [], h => by simp at h
  | [_], h => by simp at h
  | x :: y :: rest, _ => by
    simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.flushIn, minMaxOp]

theorem coreFloat_min_total {a b : Value} (ha : F32Dat a) (hb : F32Dat b) :
    ∃ v, coreFloat minI [a, b] = .ok v ∧ Dat32 v := by
  obtain ⟨xs, hxs, hl⟩ := mapM_classify (vs := [a, b]) (by simp [ha, hb])
  obtain ⟨o, ho⟩ := minI_lane xs (by simp [hl])
  refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
  simp [coreFloat, minI, ty1, floatLane, show List.range 1 = [0] from rfl, hxs, ho, bind,
    Except.bind, pure, Except.pure]

/-- **`min.f32` of two `.f32` data has an outcome**, a datum. -/
theorem minE_total {a b : Value} (ha : Dat32 a) (hb : Dat32 b) :
    ∃ v, minE [a, b] = .ok v ∧ Dat32 v := by
  have hcore : idealMin [a, b] = none → ∃ v, minE [a, b] = .ok v ∧ Dat32 v := by
    intro hn
    obtain ⟨v, hv, hdv⟩ := coreFloat_min_total ha.1 hb.1
    exact ⟨v, by unfold minE; rw [hn]; exact hv, hdv⟩
  rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
  · exact hcore (by simp [idealMin, hx, bindRead])
  rcases readEReal_dat hb.1 with hy | ⟨y, hy⟩
  · exact hcore (by simp [idealMin, hx, hy, bindRead])
  refine ⟨erealValue .f32 (min x y), ?_, dat32_erealValue _⟩
  unfold minE
  simp [idealMin, hx, hy, bindRead, pure, Except.pure]

/-- **`fma.rn.f32` of three `.f32` data has an outcome**, a datum. -/
theorem fmaE_total {a b c : Value} (ha : Dat32 a) (hb : Dat32 b) (hc : Dat32 c) :
    ∃ v, floatE (fmaI .rn false) [a, b, c] = .ok v ∧ Dat32 v := by
  unfold floatE
  cases hI : idealVal (fmaI .rn false) [a, b, c] with
  | none =>
    obtain ⟨o, ho⟩ := coreFloat_fma_rn ha.1 hb.1 hc.1
    exact ⟨_, ho, dat32_toValue o⟩
  | some r =>
    simp only [idealVal] at hI
    rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩ <;> simp only [bindRead, hx] at hI
    · cases hI
    rcases readEReal_dat hb.1 with hy | ⟨y, hy⟩ <;> simp only [hy] at hI
    · cases hI
    rcases readEReal_dat hc.1 with hz | ⟨z, hz⟩ <;> simp only [hz] at hI
    · cases hI
    rcases hm : mulEReal x y with _ | p <;> simp only [hm, Option.bind_none,
      Option.bind_some, Option.map_none, reduceCtorEq] at hI
    rcases hs : addEReal p z with _ | s <;> simp only [hs, Option.map_none, Option.map_some,
      reduceCtorEq, Option.some.injEq] at hI
    exact ⟨_, hI.symm, dat32_erealValue s⟩

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **The local step of `fma.rn.f32 d, a, b, c`** at a state writes the outcome or faults. -/
theorem exec_fmaE_at {t : TState} (hI : IdealAt A (.fma .f32) L g t)
    (hD : DeclineAt A (.fma .f32) L g t) {rnd : FloatRound} {fz : Bool} {d : Nat}
    {a b c : Opnd} {va vb vc : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb)
    (hc : OpndIs L g t c vc) :
    execLocalA A L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (floatE (fmaI rnd fz) [va, vb, vc]).map fun v => PTX.next (setReg t d v) := by
  have hf : FloatForm.ofOp (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      some (.fma .f32) := by simp [FloatForm.ofOp]
  have hi : execIdealFloat L g t (.float { fmaI rnd fz with dsts := [some d], srcs := [a, b, c] }) =
      (idealVal (fmaI rnd fz) [va, vb, vc]).map
        (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execIdealFloat, idealVal, ha.2, hb.2, hc.2, bindRead_map, Option.map_map,
      Function.comp_def, Except.map, pure, Except.pure]
  unfold floatE
  cases hv : idealVal (fmaI rnd fz) [va, vb, vc] with
  | none => rw [hD _ hf (by rw [hi, hv]; rfl), execLocal_fma_core ha hb hc]
  | some r => rw [hI _ hf _ (by rw [hi, hv]; rfl)]

/-! ### The rule -/

/-- `min.f32 d, a, b` and `fma.rn.f32 d, a, b, c` of `.f32` data. -/
def absFloat2 (env : EnvF) : Op → Option (List (Nat × TagF))
  | .float f =>
    match f.dsts, f.srcs with
    | [some d], [.reg a, .reg b] =>
      if decide (f = { minI with dsts := [some d], srcs := [.reg a, .reg b] }) &&
          d32 env a && d32 env b then some [(d, .dat32)] else none
    | [some d], [.reg a, .reg b, .reg c] =>
      if decide (f = { fmaI .rn false with dsts := [some d], srcs := [.reg a, .reg b, .reg c] }) &&
          d32 env a && d32 env b && d32 env c then some [(d, .dat32)] else none
    | _, _ => none
  | _ => none

/-- At every pc of `[a, b)` the assumptions read `min.f32` and `fma.rn.f32` as exact real
arithmetic and leave the operands the ideal rule declines to the Core rule. -/
def IdealRules2 (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b →
    (IdealAt A (.min .f32) L g t ∧ DeclineAt A (.min .f32) L g t) ∧
    (IdealAt A (.fma .f32) L g t ∧ DeclineAt A (.fma .f32) L g t)

theorem absFloat2_sound {a b : Nat} (hR : IdealRules2 A L g a b) :
    AbsSound A L g a b absFloat2 := by
  intro env op outs t h ha hb ht
  obtain ⟨⟨hI1, hD1⟩, hI2, hD2⟩ := hR t ha hb
  cases op <;> simp only [absFloat2, reduceCtorEq] at h
  rename_i f
  split at h
  · rename_i d r1 r2 _ _
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hf, h1⟩, h2⟩ := hc
    obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
    obtain ⟨y, hy, hdy⟩ := d32_ok h2 ht
    obtain ⟨v, hv, hdv⟩ := minE_total hdx hdy
    have hex := exec_minE2 (L := L) (g := g) hI1 hD1 (d := d) hx hy
    rw [hv] at hex
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
    subst hf
    exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · rename_i d r1 r2 r3 _ _
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hf, h1⟩, h2⟩, h3⟩ := hc
    obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
    obtain ⟨y, hy, hdy⟩ := d32_ok h2 ht
    obtain ⟨z, hz, hdz⟩ := d32_ok h3 ht
    obtain ⟨v, hv, hdv⟩ := fmaE_total hdx hdy hdz
    have hex := exec_fmaE_at (rnd := .rn) (fz := false) hI2 hD2 (d := d) (OpndIs.reg hx)
      (OpndIs.reg hy) (OpndIs.reg hz)
    rw [hv] at hex
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
    subst hf
    exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · simp at h

end
end PTX.Flow.TyG
