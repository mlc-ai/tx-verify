-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatH
public import Lemmas.Flow.SetpCore
public import Lemmas.Flow.Ex2Core
public import Lemmas.Flow.TypedDeclF

@[expose] public section

/-! # `ex2.approx.f32` and `setp.cmp.f32` on `.f32` data

`ex2E` and `setpE` (`Ex2Core.lean`, `SetpCore.lean`) are total on `.f32` data: the exact power
of a number, the Core table's value for an infinity or NaN (`ex2.approx` has a row for each), and
a comparison of two data, whose Core lane has a result for the six ordered operators. The power
is a datum of four bytes (`Dat32`); the comparison writes a predicate. `absFloat3` is the abstract
rule of the two. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

theorem dat32_float (r : ℝ) : Dat32 (.float .f32 r) :=
  ⟨f32Dat_float r, rfl, by intro w o n h; cases h⟩

theorem ex2I_lane (fz : Bool) (x : FVal) (h : ∀ q, x ≠ .fin q) :
    ∃ o, FloatInstr.lane (ex2I fz) [x] = some (.val o) := by
  cases x with
  | zero n => cases n <;> cases fz <;> exact ⟨_, rfl⟩
  | fin q => exact absurd rfl (h q)
  | inf n => cases n <;> cases fz <;> exact ⟨_, rfl⟩
  | nan b => cases fz <;> exact ⟨_, rfl⟩


theorem readEReal_fin {v : Value} {q : ℚ} (h : classify .f32 v = .ok (.fin q)) :
    ∃ x : ℝ, readEReal .f32 v = some (.ok (x : EReal)) := by
  cases v with
  | float f x =>
    by_cases hf : f = .f32
    · subst hf; exact ⟨x, by simp [readEReal, pure, Except.pure]⟩
    · exact ⟨q, by simp [readEReal, hf, h, readEReal.ofDatum, pure, Except.pure]⟩
  | _ => exact ⟨q, by simp [readEReal, h, readEReal.ofDatum, pure, Except.pure]⟩

theorem ex2E_total {fz : Bool} {va : Value} (ha : Dat32 va) :
    ∃ v, ex2E fz va = .ok v ∧ Dat32 v := by
  obtain ⟨c, hc⟩ := ha.1
  by_cases hn : ex2Val va = none
  · have hfin : ∀ q, c ≠ .fin q := by
      intro q hq; subst hq
      obtain ⟨x, hx⟩ := readEReal_fin hc
      simp only [ex2Val, finiteVal, hx, bindRead, EReal.coe_ne_top, EReal.coe_ne_bot, or_self,
        ↓reduceIte, EReal.toReal_coe, pure, Except.pure] at hn
      cases hn
    obtain ⟨o, ho⟩ := ex2I_lane fz c hfin
    refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
    unfold ex2E
    rw [hn]
    simp [coreFloat, ex2I, ty1, floatLane, show List.range 1 = [0] from rfl, hc, ho, bind,
      Except.bind, pure, Except.pure]
  · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    unfold ex2E
    rw [hr]
    rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
    · simp [ex2Val, finiteVal, hx, bindRead] at hr
    by_cases hb : x = ⊤ ∨ x = ⊥
    · simp [ex2Val, finiteVal, hx, hb, bindRead] at hr
    simp only [ex2Val, finiteVal, hx, hb, bindRead, ↓reduceIte, pure, Except.pure,
      Option.some.injEq] at hr
    subst hr
    exact ⟨_, rfl, dat32_float _⟩

/-- The comparison operators with a Core table (`eq`, `ne`, `lt`, `le`, `gt`, `ge`). -/
def cmpOk : Cmp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

def fcmpOk : FCmp → Bool
  | .ord c | .unord c => cmpOk c
  | _ => false

theorem fcmp_eval_total {c : FCmp} (hc : fcmpOk c = true) (a b : FVal) :
    ∃ r, c.eval a b = some r := by
  cases c <;> simp only [fcmpOk, Bool.false_eq_true] at hc <;> rename_i cmp <;>
    cases cmp <;> simp only [cmpOk, Bool.false_eq_true] at hc <;>
    simp only [FCmp.eval, Cmp.evalF] <;> split_ifs <;> exact ⟨_, rfl⟩

theorem or_of_total {o : Option Bool} (h : ∃ r, o = some r) : o = some false ∨ o = some true := by
  obtain ⟨r, rfl⟩ := h
  cases r <;> simp

theorem setpI_lane {c : FCmp} (fz : Bool) (hc : fcmpOk c = true) (xa xb : FVal) :
    ∃ r, FloatInstr.lane (setpI c fz) [xa, xb] = some (.pred r) := by
  cases fz <;>
  · simp [FloatInstr.lane, FloatInstr.rule, setpI, ty1, FloatInstr.compare, FloatInstr.flushIn]
    exact or_of_total (fcmp_eval_total hc _ _)


theorem fcmpOk_cmp {c : FCmp} (h : fcmpOk c = true) : ∃ cmp, c = .ord cmp ∨ c = .unord cmp := by
  cases c <;> simp only [fcmpOk, Bool.false_eq_true] at h
  · exact ⟨_, .inl rfl⟩
  · exact ⟨_, .inr rfl⟩

/-- **A comparison of two `.f32` data has an outcome.** -/
theorem setpE_total {c : FCmp} {fz : Bool} {va vb : Value} (hc : fcmpOk c = true)
    (ha : F32Dat va) (hb : F32Dat vb) : ∃ r, setpE c fz va vb = .ok r := by
  obtain ⟨cmp, hcmp⟩ := fcmpOk_cmp hc
  have hbase : ∃ cm, fcmpBase c = some cm := by rcases hcmp with rfl | rfl <;> exact ⟨_, rfl⟩
  obtain ⟨cm, hcm⟩ := hbase
  have hcore : idealSetp c va vb = none → ∃ r, setpE c fz va vb = .ok r := by
    intro hn
    obtain ⟨xa, hxa⟩ := ha
    obtain ⟨xb, hxb⟩ := hb
    obtain ⟨r, hr⟩ := setpI_lane (c := c) fz hc xa xb
    refine ⟨r, ?_⟩
    unfold setpE
    rw [hn]
    simp [coreSetp, setpI, ty1, hxa, hxb, hr, bind, Except.bind, pure, Except.pure]
  rcases readEReal_dat ha with hx | ⟨x, hx⟩
  · exact hcore (by simp [idealSetp, hcm, hx, bindRead])
  rcases readEReal_dat hb with hy | ⟨y, hy⟩
  · exact hcore (by simp [idealSetp, hcm, hx, hy, bindRead])
  refine ⟨erealCompare cm x y, ?_⟩
  unfold setpE
  simp [idealSetp, hcm, hx, hy, bindRead, pure, Except.pure]


variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `ex2.approx{.ftz}.f32 d, a` and `setp.cmp{.ftz}.f32 p, a, b` of `.f32` data. -/
def absFloat3 (env : EnvF) : Op → Option (List (Nat × TagF))
  | .float f =>
    match f.dsts, f.srcs, f.op with
    | [some d], [.reg a], .ex2 =>
      if decide (f = { ex2I f.ftz with dsts := [some d], srcs := [.reg a] }) && d32 env a then
        some [(d, .dat32)] else none
    | [some p], [a, b], .setp c none =>
      if decide (f = { setpI c f.ftz with dsts := [some p], srcs := [a, b] }) && fcmpOk c &&
          d32o env a && d32o env b then some [(p, .old .pred)] else none
    | _, _, _ => none
  | _ => none

/-- At every pc of `[a, b)` the assumptions read `ex2.approx` as the exact power and `setp` as the
comparison of extended reals, and leave the declined operands to the Core rule. -/
def IdealRules3 (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b →
    (ApproxAt A (.ex2 .f32) L g t ∧ ApproxDeclineAt A (.ex2 .f32) L g t) ∧
    (IdealAt A (.setp .f32) L g t ∧ DeclineAt A (.setp .f32) L g t) ∧
    (IdealAt A (.setpInf .f32) L g t ∧ DeclineAt A (.setpInf .f32) L g t)

theorem absFloat3_sound {a b : Nat} (hR : IdealRules3 A L g a b) :
    AbsSound A L g a b absFloat3 := by
  intro env op outs t h ha hb ht
  obtain ⟨⟨hA, hAD⟩, ⟨hI, hD⟩, hJ, hJD⟩ := hR t ha hb
  cases op <;> simp only [absFloat3, reduceCtorEq] at h
  rename_i f
  split at h
  · rename_i d a hd hs ho
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hf, h1⟩ := hc
    obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
    obtain ⟨v, hv, hdv⟩ := ex2E_total (fz := f.ftz) hdx
    have hex := exec_ex2E hA hAD (fz := f.ftz) (d := d) (OpndIs.reg hx)
    rw [hv] at hex
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
    rw [hf]
    exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · rename_i p r1 r2 c hd hs ho
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hf, hok⟩, h1⟩, h2⟩ := hc
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) h1 ht
    obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) h2 ht
    obtain ⟨r, hr⟩ := setpE_total (c := c) (fz := f.ftz) hok hda.1 hdb.1
    obtain ⟨cmp, hcmp⟩ := fcmpOk_cmp hok
    have hex : execLocalA A L g t
        (.float { setpI c f.ftz with dsts := [some p], srcs := [r1, r2] }) =
        .ok (PTX.next (setReg t p (.pred r))) := by
      by_cases hinf : (isInfConst r1 || isInfConst r2) = true
      · have := exec_setpInfE hJ hJD (fz := f.ftz) (p := p) hcmp hinf hva hvb
        rw [hr] at this; exact this
      · have hi : isInfConst r1 = false ∧ isInfConst r2 = false := by simpa using hinf
        have := exec_setpE hI hD (fz := f.ftz) (p := p) hcmp hi.1 hi.2 hva hvb
        rw [hr] at this; exact this
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := p) (tg := .old .pred) (v := .pred r) ⟨r, rfl⟩
    rw [hf]
    exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · simp at h

end
end PTX.Flow.TyG
