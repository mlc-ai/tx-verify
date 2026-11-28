-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedMoveF
public import Lemmas.Flow.FloatDat
public import Lemmas.Flow.FmaPairCore

@[expose] public section

/-! # `max.f32` and `fma.rn.f32x2` on `.f32` data

`maxE` and `fma2E` (`MaxCore.lean`, `FmaPairCore.lean`) are the outcomes of the two instructions
under an ideal-real assumption that leaves its declines to the Core rule. They are total on
`.f32` data: the ideal rule reads a datum in the extended reals or declines a NaN, and the Core
rule's lane has a result for every data (`minMaxOp` is total, `Layout.roundVal` to nearest is
total). The outcome is again a datum of four bytes, no slice (`Dat32`), or a pair of two. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

theorem dat32_toValue (c : FVal) : Dat32 (c.toValue .f32) :=
  ⟨f32Dat_toValue c, toValue_f32_bytes c, by
    rcases c with neg | q | neg | p
    · cases neg <;> simp [FVal.toValue]
    · simp [FVal.toValue]
    · simp [FVal.toValue]
    · cases p <;> simp [FVal.toValue]⟩

theorem dat32_erealValue (r : EReal) : Dat32 (erealValue .f32 r) :=
  ⟨f32Dat_erealValue r, erealValue_f32_bytes r, by
    unfold erealValue
    split_ifs <;> simp [FVal.toValue]⟩

theorem mapM_classify {vs : List Value} (h : ∀ v ∈ vs, F32Dat v) :
    ∃ xs, vs.mapM (fun v => (classify .f32 v : Exec FVal)) = .ok xs ∧ xs.length = vs.length := by
  induction vs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons v vs ih =>
    obtain ⟨c, hc⟩ := h v (by simp)
    obtain ⟨xs, hxs, hl⟩ := ih (fun w hw => h w (by simp [hw]))
    exact ⟨c :: xs, by simp [List.mapM_cons, hc, hxs, bind, Except.bind, pure, Except.pure],
      by simp [hl]⟩

/-- The Core lane of `max.f32` has a value for every two or three data. -/
theorem maxI_lane : ∀ xs : List FVal, 2 ≤ xs.length → ∃ o, FloatInstr.lane maxI xs = some (.val o)
  | [], h => by simp at h
  | [_], h => by simp at h
  | x :: y :: rest, _ => by
    simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.flushIn, minMaxOp]

theorem coreFloat_max_total {vs : List Value} (hd : ∀ v ∈ vs, F32Dat v) (h2 : 2 ≤ vs.length) :
    ∃ v, coreFloat maxI vs = .ok v ∧ Dat32 v := by
  obtain ⟨xs, hxs, hl⟩ := mapM_classify hd
  obtain ⟨o, ho⟩ := maxI_lane xs (by omega)
  refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
  simp [coreFloat, maxI, ty1, floatLane, show List.range 1 = [0] from rfl, hxs, ho, bind,
    Except.bind, pure, Except.pure]

/-- **`max.f32` of two or three `.f32` data has an outcome**, a datum. -/
theorem maxE_total {vs : List Value} (hd : ∀ v ∈ vs, Dat32 v) (h2 : 2 ≤ vs.length)
    (h3 : vs.length ≤ 3) : ∃ v, maxE vs = .ok v ∧ Dat32 v := by
  have hf : ∀ v ∈ vs, F32Dat v := fun v hv => (hd v hv).1
  have hcore : ∀ r, idealMax vs = r → r = none → ∃ v, maxE vs = .ok v ∧ Dat32 v := by
    intro r hr hn
    obtain ⟨v, hv, hdv⟩ := coreFloat_max_total hf h2
    exact ⟨v, by unfold maxE; rw [hr, hn]; exact hv, hdv⟩
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  · simp at h2
  · simp at h2
  · have ha := hf a (by simp)
    have hb := hf b (by simp)
    rcases readEReal_dat ha with hx | ⟨x, hx⟩
    · exact hcore _ rfl (by simp [idealMax, hx, bindRead])
    rcases readEReal_dat hb with hy | ⟨y, hy⟩
    · exact hcore _ rfl (by simp [idealMax, hx, hy, bindRead])
    refine ⟨erealValue .f32 (max x y), ?_, dat32_erealValue _⟩
    unfold maxE
    simp [idealMax, hx, hy, bindRead, pure, Except.pure]
  · have ha := hf a (by simp)
    have hb := hf b (by simp)
    have hc := hf c (by simp)
    rcases readEReal_dat ha with hx | ⟨x, hx⟩
    · exact hcore _ rfl (by simp [idealMax, hx, bindRead])
    rcases readEReal_dat hb with hy | ⟨y, hy⟩
    · exact hcore _ rfl (by simp [idealMax, hx, hy, bindRead])
    rcases readEReal_dat hc with hz | ⟨z, hz⟩
    · exact hcore _ rfl (by simp [idealMax, hx, hy, hz, bindRead])
    refine ⟨erealValue .f32 (max (max x y) z), ?_, dat32_erealValue _⟩
    unfold maxE
    simp [idealMax, hx, hy, hz, bindRead, pure, Except.pure]
  · simp only [List.length_cons] at h3; omega

/-! ### `fma.rn.f32x2` -/

theorem roundVal_total (w : FVal) : ∃ o, FloatFmt.f32.layout.roundVal .rn false w = some o := by
  cases w with
  | fin q =>
    obtain ⟨o, ho⟩ := round_f32_rn (q : ℝ) false
    exact ⟨o, by simp [Layout.roundVal, Layout.roundFtz, ho]⟩
  | _ => exact ⟨_, rfl⟩

theorem fma2I_lane (xa xb xc : FVal) :
    ∃ o, FloatInstr.lane fma2I [xa, xb, xc] = some (.val o) := by
  obtain ⟨o, ho⟩ := roundVal_total ((xa.mul xb).add .rn xc)
  exact ⟨o, by simp [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee, FloatInstr.arith,
    FloatInstr.flushIn, FloatRound.mode, fma2I, ho]⟩

theorem dat64_split_f32 {x : Value} (h : Dat64 x) :
    F32Dat (splitValue 64 x).1 ∧ F32Dat (splitValue 64 x).2 :=
  ⟨(dat64_split h).2.1.1, (dat64_split h).2.2.1⟩

theorem coreFloat_fma2_total {va vb vc : Value} (ha : Dat64 va) (hb : Dat64 vb)
    (hc : Dat64 vc) : ∃ v, coreFloat fma2I [va, vb, vc] = .ok v ∧ Dat64 v := by
  obtain ⟨xa, hxa⟩ := (dat64_split_f32 ha).1
  obtain ⟨xb, hxb⟩ := (dat64_split_f32 hb).1
  obtain ⟨xc, hxc⟩ := (dat64_split_f32 hc).1
  obtain ⟨ya, hya⟩ := (dat64_split_f32 ha).2
  obtain ⟨yb, hyb⟩ := (dat64_split_f32 hb).2
  obtain ⟨yc, hyc⟩ := (dat64_split_f32 hc).2
  obtain ⟨o0, h0⟩ := fma2I_lane xa xb xc
  obtain ⟨o1, h1⟩ := fma2I_lane ya yb yc
  refine ⟨.pair (o0.toValue .f32) (o1.toValue .f32), ?_,
    .inr ⟨_, _, rfl, dat32_toValue _, dat32_toValue _⟩⟩
  simp [coreFloat, floatLane, FloatFmt.bytes, show List.range 2 = [0, 1] from rfl, hxa, hxb,
    hxc, hya, hyb, hyc, h0, h1, bind, Except.bind, pure, Except.pure]

theorem pairRead_dat {v : Value} (h : Dat64 v) :
    pairRead v = none ∨ ∃ p, pairRead v = some (.ok p) := by
  obtain ⟨h1, h2⟩ := dat64_split_f32 h
  unfold pairRead
  rcases readEReal_dat h1 with e1 | ⟨x, e1⟩ <;> rcases readEReal_dat h2 with e2 | ⟨y, e2⟩ <;>
    simp [e1, e2, pure, Except.pure]

/-- **`fma.rn.f32x2` of three 64-bit values of data has an outcome**, a pair of data. -/
theorem fma2E_total {va vb vc : Value} (ha : Dat64 va) (hb : Dat64 vb) (hc : Dat64 vc) :
    ∃ v, fma2E va vb vc = .ok v ∧ Dat64 v := by
  have hcore : idealFma2 va vb vc = none → ∃ v, fma2E va vb vc = .ok v ∧ Dat64 v := by
    intro hn
    obtain ⟨v, hv, hd⟩ := coreFloat_fma2_total ha hb hc
    exact ⟨v, by unfold fma2E; rw [hn]; exact hv, hd⟩
  rcases pairRead_dat ha with e1 | ⟨⟨x0, x1⟩, e1⟩
  · exact hcore (by simp [idealFma2, e1, bindRead])
  rcases pairRead_dat hb with e2 | ⟨⟨y0, y1⟩, e2⟩
  · exact hcore (by simp [idealFma2, e1, e2, bindRead])
  rcases pairRead_dat hc with e3 | ⟨⟨z0, z1⟩, e3⟩
  · exact hcore (by simp [idealFma2, e1, e2, e3, bindRead])
  rcases h0 : (mulEReal x0 y0).bind (addEReal · z0) with _ | r0
  · exact hcore (by simp [idealFma2, e1, e2, e3, bindRead, h0])
  rcases h1 : (mulEReal x1 y1).bind (addEReal · z1) with _ | r1
  · exact hcore (by simp [idealFma2, e1, e2, e3, bindRead, h0, h1])
  refine ⟨.pair (erealValue .f32 r0) (erealValue .f32 r1), ?_,
    .inr ⟨_, _, rfl, dat32_erealValue _, dat32_erealValue _⟩⟩
  unfold fma2E
  simp [idealFma2, e1, e2, e3, bindRead, h0, h1, pure, Except.pure]

/-! ### The rules -/

/-- A register of tag `.dat64`. -/
def d64 (env : EnvF) (r : Nat) : Bool := TagF.sat (env.lookup r) .dat64

theorem d64_ok {env : EnvF} {t : TState} {r : Nat} (h : d64 env r = true) (ht : TypedF env t) :
    ∃ x, t.regs r = some x ∧ Dat64 x :=
  TagF.sat_ok (v := t.regs r) (need := .dat64) h (fun tg e => ht r tg e)

/-- `max.f32 d, a, b` and `max.f32 d, a, b, c` of `.f32` data, and `fma.rn.f32x2 d, a, b, c` of
64-bit values of data. -/
def absFloat (env : EnvF) : Op → Option (List (Nat × TagF))
  | .float f =>
    match f.dsts, f.srcs with
    | [some d], [.reg a, .reg b] =>
      if decide (f = { maxI with dsts := [some d], srcs := [.reg a, .reg b] }) &&
          d32 env a && d32 env b then some [(d, .dat32)] else none
    | [some d], [.reg a, .reg b, .reg c] =>
      if decide (f = { maxI with dsts := [some d], srcs := [.reg a, .reg b, .reg c] }) &&
          d32 env a && d32 env b && d32 env c then some [(d, .dat32)]
      else if decide (f = { fma2I with dsts := [some d], srcs := [.reg a, .reg b, .reg c] }) &&
          d64 env a && d64 env b && d64 env c then some [(d, .dat64)] else none
    | _, _ => none
  | _ => none

/-- At every pc of `[a, b)` the assumptions read `max.f32` and `fma.rn.f32x2` as exact real
arithmetic and leave the operands the ideal rule declines to the Core rule. -/
def IdealRules (A : List Assumption) (L : Launch) (g a b : Nat) : Prop :=
  ∀ t : TState, a ≤ t.pc → t.pc < b →
    (IdealAt A (.max .f32) L g t ∧ DeclineAt A (.max .f32) L g t) ∧
    (IdealAt A .fmaRnF32x2 L g t ∧ DeclineAt A .fmaRnF32x2 L g t)

variable {A : List Assumption} {L : Launch} {g : Nat}

theorem absFloat_sound {a b : Nat} (hR : IdealRules A L g a b) :
    AbsSound A L g a b absFloat := by
  intro env op outs t h ha hb ht
  obtain ⟨⟨hI1, hD1⟩, hI2, hD2⟩ := hR t ha hb
  cases op <;> simp only [absFloat, reduceCtorEq] at h
  rename_i f
  split at h
  · rename_i d r1 r2 _ _
    split_ifs at h with hc
    obtain rfl := Option.some.inj h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hf, h1⟩, h2⟩ := hc
    obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
    obtain ⟨y, hy, hdy⟩ := d32_ok h2 ht
    obtain ⟨v, hv, hdv⟩ := maxE_total (vs := [x, y]) (by simp [hdx, hdy]) (by simp) (by simp)
    have hex := exec_maxE2 (L := L) (g := g) hI1 hD1 (d := d) hx hy
    rw [hv] at hex
    obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
    subst hf
    exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · rename_i d r1 r2 r3 _ _
    split_ifs at h with hc hc2
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hf, h1⟩, h2⟩, h3⟩ := hc
      obtain ⟨x, hx, hdx⟩ := d32_ok h1 ht
      obtain ⟨y, hy, hdy⟩ := d32_ok h2 ht
      obtain ⟨z, hz, hdz⟩ := d32_ok h3 ht
      obtain ⟨v, hv, hdv⟩ := maxE_total (vs := [x, y, z]) (by simp [hdx, hdy, hdz]) (by simp)
        (by simp)
      have hex := exec_maxE3 (L := L) (g := g) hI1 hD1 (d := d) hx hy hz
      rw [hv] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat32) ⟨_, rfl, hdv⟩
      subst hf
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
    · obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2
      obtain ⟨⟨⟨hf, h1⟩, h2⟩, h3⟩ := hc2
      obtain ⟨x, hx, hdx⟩ := d64_ok h1 ht
      obtain ⟨y, hy, hdy⟩ := d64_ok h2 ht
      obtain ⟨z, hz, hdz⟩ := d64_ok h3 ht
      obtain ⟨v, hv, hdv⟩ := fma2E_total hdx hdy hdz
      have hex := exec_fma2E (L := L) (g := g) hI2 hD2 (d := d) hx hy hz
      rw [hv] at hex
      obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := .dat64) ⟨_, rfl, hdv⟩
      subst hf
      exact ⟨_, hex, rfl, rfl, rfl, rfl, hw1, hw2⟩
  · simp at h

end
end PTX.Flow.TyG
