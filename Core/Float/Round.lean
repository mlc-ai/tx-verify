-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Format
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Rounding an exact number to a layout

The one rounding function of the model: an exact real number rounded to a floating or fixed-point
layout by a rounding mode, with an overflow policy.
-/

namespace PTX

noncomputable section

/-! ## THREAD-FLOAT-ROUND — rounding an exact number to a layout
Statement: An exact real number is rounded to a layout by one of the rounding modes `.rn`, `.rz`,
  `.rm`, `.rp` and `.rs`, with IEEE 754 overflow or `.satfinite` saturation. Where the manual
  leaves the result open, the rounding has no result.

Defs: RoundMode, Overflow, FloatRound.mode, RoundMode.away, RoundMode.applies, Layout.fixedVal,
  Layout.round, FloatFmt.overflow, FloatFmt.maxField, FloatFmt.encode, Layout.findGreatest_mag,
  Layout.maxNorm_binary, Layout.mag_le_maxNorm, Layout.round_zero, Layout.round_exact,
  Layout.round_between, Layout.round_satfinite, Layout.round_inf_none, Layout.round_inf_ieee,
  Layout.round_unsigned_below, RoundMode.away_rz, RoundMode.away_rm, RoundMode.away_rp,
  RoundMode.away_rn_lt, RoundMode.away_rn_gt, RoundMode.away_rn_tie, RoundMode.away_rs,
  Layout.maxNorm_fixed, Layout.maxNorm_fixed_nonneg, Layout.round_fixed_rs, Layout.round_fixed_zero,
  Layout.round_fixed_over, Layout.round_fixed_under, Layout.round_fixed_exact,
  Layout.round_fixed_between, FloatFmt.layout_facts, FloatFmt.encode_fieldVal, FloatFmt.encode_eq,
  FloatFmt.decode_number, FloatFmt.decode_encode_of_decode, FloatFmt.decode_encode

Source:
- §6.5.2: ".rn rounds to nearest even .rna rounds to nearest, ties away from zero .rz rounds
    toward zero .rm rounds toward negative infinity .rp rounds toward positive infinity .rs rounds
    either toward zero or away from zero based on the carry out of the integer addition of random
    bits and the discarded bits of mantissa"
- §9.7.3.3: "Rounding modifiers: .rn mantissa LSB rounds to nearest even .rz mantissa LSB rounds
    toward zero .rm mantissa LSB rounds toward negative infinity .rp mantissa LSB rounds toward
    positive infinity"
- §9.7.10.24: "Operation’s result is rounded in the direction toward zero or away from zero based
    on the carry out of the integer addition of the supplied random bits ( rbits ) to the truncated
    off (discarded) bits of mantissa from the input."
- §9.7.10.24: "If the absolute value of input (ignoring sign) is greater than MAX_NORM of the
    specified destination format, then the result is sign-preserved MAX_NORM of the destination
    format and a positive MAX_NORM in .ue8m0x2 and .ue5m3x2 for which the destination sign is not
    supported."
- §5.2.4: "Positive max representation = 01.111111 = 127 * 2^(-6) = 1.984375 Negative max
    representation = 10.000000 = -128 * 2^(-6) = -2.0"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."

Direction: stricter

Applies: The rounding of an exact result or an exact source value to a destination layout

Premises: None.

Effect: Local evaluation. A value of the layout is its own result. Otherwise `lo` and `hi` are the
  neighbouring finite values of the layout in the code order: `.rz` takes the one nearer to zero,
  `.rm` the lower, `.rp` the higher, and `.rn` the nearer one, at the midpoint the one with the
  even code (the even mantissa of a binary layout, the even integer of a fixed-point layout). A
  binary layout with a zero-width mantissa has no result at a midpoint. Underflow is gradual, and a
  nonzero number that rounds to the zero field gives the zero of its sign; an exact zero gives the
  zero with the sign `zneg` the caller supplies, and the one zero of a fixed-point layout.
  Overflow with `Overflow.satfinite`: a magnitude above MAX_NORM gives the MAX_NORM of the sign of
  the number (positive for an unsigned layout). Overflow with `Overflow.inf` follows IEEE 754 for
  a layout with infinities: `.rn` gives the infinity from the midpoint between MAX_NORM and
  `2^(emax+1)` on, `.rz` gives MAX_NORM, `.rm` gives the infinity for a negative number only and
  `.rp` for a positive number only; a layout without infinity has no result. An unsigned layout
  has no result below its smallest positive value, which includes zero, negative numbers and the
  `.ue8m0` pattern `0`. For a fixed-point layout, a number below the negative of MAX_NORM has no
  result, since the sign-preserved MAX_NORM can be read as `-MAX_NORM` or as the negative maximum
  (for `.s2f6`, `-1.984375` or `-2.0`). `.rs k r` adds the `k`-bit random number `r` to the `D`
  discarded units: it applies to an `.f32` value that is zero or at least the smallest normal
  magnitude of a binary layout and lies `D` units of `2^-k` result ulps above the neighbour `t`
  nearer to zero, and gives the neighbour away from zero when `D + r ≥ 2^k` and `t` otherwise;
  overflow is decided on the input, and `.rs` has no result for a subnormal result, for `r ≥ 2^k`,
  for a fixed-point layout or with `Overflow.inf` above MAX_NORM.
-/

/-- A floating rounding mode (Table 17). `.rna` is left out, since only `.tf32` conversions use
it. `rs k r` is `.rs` with `k` discarded mantissa bits and the random bits `r`. -/
inductive RoundMode where
  | rn | rz | rm | rp
  | rs (k r : Nat)
  deriving DecidableEq, Repr

/-- The overflow policy: IEEE 754 overflow, or saturation to MAX_NORM (`.satfinite`). -/
inductive Overflow where
  | inf | satfinite
  deriving DecidableEq, Repr

/-- The rounding mode of an instruction's rounding modifier. -/
def FloatRound.mode : FloatRound → RoundMode
  | .rn => .rn
  | .rz => .rz
  | .rm => .rm
  | .rp => .rp

open Classical in
/-- Whether a number of magnitude `a` and sign `neg`, strictly between the neighbouring
magnitudes `t` (nearer to zero) and `u`, rounds away from zero; `none` where the result is open.
`tEven` is the parity of the code of `t` when ties are determined. -/
def RoundMode.away (m : RoundMode) (neg : Bool) (a t u : ℝ) (tEven : Option Bool) :
    Option Bool :=
  match m with
  | .rz => some false
  | .rm => some neg
  | .rp => some !neg
  | .rn =>
    if a - t < u - a then some false
    else if u - a < a - t then some true
    else tEven.map (!·)
  | .rs k r =>
    if ∃ D : ℕ, (a - t) * 2 ^ k = D * (u - t) then
      some (decide ((2 : ℝ) ^ k ≤ (a - t) * 2 ^ k / (u - t) + r))
    else none

/-- The inputs a rounding mode applies to on a binary layout: `.rs k r` takes `k`-bit random
bits and an `.f32` value that is zero or at least the smallest normal magnitude of the layout;
every other mode applies to every number. -/
def RoundMode.applies (m : RoundMode) (L : Layout) (x : ℝ) : Prop :=
  match m with
  | .rs k r => r < 2 ^ k ∧ FloatFmt.f32.representable x ∧
      (x = 0 ∨ ((L.minNormal : ℚ) : ℝ) ≤ |x|)
  | _ => True

/-- The datum of the integer `j` of a fixed-point layout with `frac` fraction bits, negated when
`neg`; the integer `0` is the one zero `+0`. -/
def Layout.fixedVal (frac j : Nat) (neg : Bool) : FVal :=
  if j = 0 then .zero false else .fin ((if neg then -(j : ℚ) else j) * (2 : ℚ) ^ (-(frac : ℤ)))

open Classical in
/-- The `L` datum of the exact number `x` rounded by `m` with the overflow policy `ov`; `zneg`
is the sign of an exact zero. `none` where the manual leaves the result open. -/
def Layout.round (L : Layout) (m : RoundMode) (ov : Overflow) (x : ℝ) (zneg : Bool) :
    Option FVal :=
  let neg := decide (x < 0)
  let a := |x|
  match L with
  | .binary eb mb signed sp =>
    let Lb := Layout.binary eb mb signed sp
    let mag (F : Nat) : ℝ := (Layout.magnitude eb mb F : ℚ)
    if ¬m.applies Lb x then none
    else if x = 0 then (if signed then some (.zero zneg) else none)
    else if ((Lb.maxNorm : ℚ) : ℝ) < a then
      match ov with
      | .satfinite =>
        some (.fin (if neg && signed then -Lb.maxNorm else Lb.maxNorm))
      | .inf =>
        if sp = .ieee ∧ signed then
          let top := Layout.fieldVal eb mb Lb.topField neg
          match m with
          | .rn => if a < (mag Lb.topField + mag (Lb.topField + 1)) / 2 then some top
            else some (.inf neg)
          | .rz => some top
          | .rm => if neg then some (.inf neg) else some top
          | .rp => if neg then some top else some (.inf neg)
          | .rs .. => none
        else none
    else if signed = false ∧ x < mag 1 then none
    else
      let lo := Nat.findGreatest (fun F => mag F ≤ a) Lb.topField
      if mag lo = a then some (Layout.fieldVal eb mb lo neg)
      else (m.away neg a (mag lo) (mag (lo + 1)) (if mb = 0 then none else some (lo % 2 == 0))).map
        fun up => Layout.fieldVal eb mb (if up then lo + 1 else lo) neg
  | .fixed w frac =>
    let Lf := Layout.fixed w frac
    let s : ℝ := 2 ^ frac
    match m with
    | .rs .. => none
    | _ =>
      if x = 0 then some (.zero false)
      else if ((Lf.maxNorm : ℚ) : ℝ) < a then
        if ov = .satfinite ∧ 0 < x then some (.fin Lf.maxNorm) else none
      else
        let k := ⌊a * s⌋.toNat
        if (k : ℝ) = a * s then some (Layout.fixedVal frac k neg)
        else (m.away neg a (k / s) ((k + 1) / s) (some (k % 2 == 0))).map
          fun up => Layout.fixedVal frac (if up then k + 1 else k) neg


/-! Characterization lemmas: `round` is noncomputable, so instances are computed through these. -/

theorem Layout.findGreatest_mag {eb mb F top : Nat} {a : ℝ} (hF : F ≤ top)
    (h1 : ((Layout.magnitude eb mb F : ℚ) : ℝ) ≤ a)
    (h2 : a < ((Layout.magnitude eb mb (F + 1) : ℚ) : ℝ)) :
    Nat.findGreatest (fun G => ((Layout.magnitude eb mb G : ℚ) : ℝ) ≤ a) top = F := by
  rw [Nat.findGreatest_eq_iff]
  refine ⟨hF, fun _ => h1, fun n hn _ hle => ?_⟩
  have : Layout.magnitude eb mb (F + 1) ≤ Layout.magnitude eb mb n :=
    (Layout.magnitude_strictMono eb mb).monotone hn
  have : ((Layout.magnitude eb mb (F + 1) : ℚ) : ℝ) ≤ Layout.magnitude eb mb n := by
    exact_mod_cast this
  linarith

theorem Layout.maxNorm_binary (eb mb : Nat) (signed : Bool) (sp : Specials) :
    (Layout.binary eb mb signed sp).maxNorm =
      Layout.magnitude eb mb (Layout.binary eb mb signed sp).topField := rfl

theorem Layout.mag_le_maxNorm {eb mb : Nat} {signed : Bool} {sp : Specials} {F : Nat}
    (hF : F ≤ (Layout.binary eb mb signed sp).topField) :
    ((Layout.magnitude eb mb F : ℚ) : ℝ) ≤ (((Layout.binary eb mb signed sp).maxNorm : ℚ) : ℝ) := by
  rw [Layout.maxNorm_binary]
  exact_mod_cast (Layout.magnitude_strictMono eb mb).monotone hF

/-- An exact zero gives the zero of the sign `zneg` on a signed binary layout. -/
theorem Layout.round_zero {eb mb : Nat} {sp : Specials} {m : RoundMode} {ov : Overflow}
    {zneg : Bool} (hm : m.applies (.binary eb mb true sp) 0) :
    (Layout.binary eb mb true sp).round m ov 0 zneg = some (.zero zneg) := by
  simp [Layout.round, hm]

/-- A value of a binary layout, the signed magnitude of a nonzero field up to `topField`,
rounds to itself. -/
theorem Layout.round_exact {eb mb : Nat} {signed : Bool} {sp : Specials} {m : RoundMode}
    {ov : Overflow} {x : ℝ} {zneg : Bool} {F : Nat}
    (hm : m.applies (.binary eb mb signed sp) x) (hF0 : 0 < F)
    (hF : F ≤ (Layout.binary eb mb signed sp).topField)
    (hx : |x| = ((Layout.magnitude eb mb F : ℚ) : ℝ)) (hs : signed = false → 0 ≤ x) :
    (Layout.binary eb mb signed sp).round m ov x zneg =
      some (Layout.fieldVal eb mb F (decide (x < 0))) := by
  have hpos : (0 : ℝ) < ((Layout.magnitude eb mb F : ℚ) : ℝ) := by
    exact_mod_cast Layout.magnitude_pos hF0
  have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at hx; linarith
  have hmax := Layout.mag_le_maxNorm hF
  have hlt : ((Layout.magnitude eb mb F : ℚ) : ℝ) < ((Layout.magnitude eb mb (F + 1) : ℚ) : ℝ) := by
    exact_mod_cast Layout.magnitude_lt_succ eb mb F
  have hu : ¬ (signed = false ∧ x < ((Layout.magnitude eb mb 1 : ℚ) : ℝ)) := by
    rintro ⟨h1, h2⟩
    have h3 : ((Layout.magnitude eb mb 1 : ℚ) : ℝ) ≤ ((Layout.magnitude eb mb F : ℚ) : ℝ) := by
      exact_mod_cast (Layout.magnitude_strictMono eb mb).monotone hF0
    rw [abs_of_nonneg (hs h1)] at hx
    linarith
  have hfg := Layout.findGreatest_mag (top := (Layout.binary eb mb signed sp).topField) hF
    (le_of_eq hx.symm) (by rw [hx]; exact hlt)
  simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, hu, hfg]
  simp only [hx, not_lt.mpr hmax, ↓reduceIte]

/-- A number strictly between the magnitudes of the consecutive fields `F` and `F + 1` rounds to
one of them as `RoundMode.away` decides. -/
theorem Layout.round_between {eb mb : Nat} {signed : Bool} {sp : Specials} {m : RoundMode}
    {ov : Overflow} {x : ℝ} {zneg : Bool} {F : Nat}
    (hm : m.applies (.binary eb mb signed sp) x)
    (hF : F < (Layout.binary eb mb signed sp).topField)
    (h1 : ((Layout.magnitude eb mb F : ℚ) : ℝ) < |x|)
    (h2 : |x| < ((Layout.magnitude eb mb (F + 1) : ℚ) : ℝ))
    (hs : signed = false → 0 < F ∧ 0 ≤ x) :
    (Layout.binary eb mb signed sp).round m ov x zneg =
      (m.away (decide (x < 0)) |x| (Layout.magnitude eb mb F : ℚ)
        (Layout.magnitude eb mb (F + 1) : ℚ) (if mb = 0 then none else some (F % 2 == 0))).map
        fun up => Layout.fieldVal eb mb (if up then F + 1 else F) (decide (x < 0)) := by
  have h0 : (0 : ℝ) ≤ ((Layout.magnitude eb mb F : ℚ) : ℝ) := by
    exact_mod_cast Layout.magnitude_nonneg eb mb F
  have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at h1; linarith
  have hmax := Layout.mag_le_maxNorm (show F + 1 ≤ _ from hF)
  have hu : ¬ (signed = false ∧ x < ((Layout.magnitude eb mb 1 : ℚ) : ℝ)) := by
    rintro ⟨hs1, hs2⟩
    obtain ⟨hF0, hx⟩ := hs hs1
    have h3 : ((Layout.magnitude eb mb 1 : ℚ) : ℝ) ≤ ((Layout.magnitude eb mb F : ℚ) : ℝ) := by
      exact_mod_cast (Layout.magnitude_strictMono eb mb).monotone hF0
    rw [abs_of_nonneg hx] at h1
    linarith
  have hfg := Layout.findGreatest_mag (top := (Layout.binary eb mb signed sp).topField)
    hF.le h1.le h2
  have hne : ((Layout.magnitude eb mb F : ℚ) : ℝ) ≠ |x| := ne_of_lt h1
  simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, hu, hfg, hne]
  simp only [not_lt.mpr (le_of_lt (lt_of_lt_of_le h2 hmax)), ↓reduceIte]

/-- Overflow with `.satfinite`: the MAX_NORM of the sign of `x` (positive for an unsigned
layout). -/
theorem Layout.round_satfinite {eb mb : Nat} {signed : Bool} {sp : Specials} {m : RoundMode}
    {x : ℝ} {zneg : Bool} (hm : m.applies (.binary eb mb signed sp) x)
    (hx : (((Layout.binary eb mb signed sp).maxNorm : ℚ) : ℝ) < |x|) :
    (Layout.binary eb mb signed sp).round m .satfinite x zneg =
      some (.fin (if decide (x < 0) && signed then -(Layout.binary eb mb signed sp).maxNorm
        else (Layout.binary eb mb signed sp).maxNorm)) := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx
    have := Layout.mag_le_maxNorm (eb := eb) (mb := mb) (signed := signed) (sp := sp)
      (F := 0) (Nat.zero_le _)
    rw [Layout.magnitude_zero] at this; push_cast at this; linarith
  simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, hx]

/-- Overflow with `Overflow.inf` on a layout without infinities, or an unsigned one: no result. -/
theorem Layout.round_inf_none {eb mb : Nat} {signed : Bool} {sp : Specials} {m : RoundMode}
    {x : ℝ} {zneg : Bool} (hsp : ¬ (sp = .ieee ∧ signed = true))
    (hx : (((Layout.binary eb mb signed sp).maxNorm : ℚ) : ℝ) < |x|) :
    (Layout.binary eb mb signed sp).round m .inf x zneg = none := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx
    have := Layout.mag_le_maxNorm (eb := eb) (mb := mb) (signed := signed) (sp := sp)
      (F := 0) (Nat.zero_le _)
    rw [Layout.magnitude_zero] at this; push_cast at this; linarith
  by_cases hm : m.applies (.binary eb mb signed sp) x
  · simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, hx, hsp]
  · simp only [Layout.round, hm, not_false_eq_true, ↓reduceIte]

/-- IEEE overflow with `Overflow.inf` on a signed IEEE layout, by mode: `.rn` gives the infinity
from the midpoint between MAX_NORM and the magnitude of the infinity field on, `.rz` MAX_NORM,
`.rm` the infinity for a negative number, `.rp` for a positive one; `.rs` has no result. -/
theorem Layout.round_inf_ieee {eb mb : Nat} {m : RoundMode} {x : ℝ} {zneg : Bool}
    (hm : m.applies (.binary eb mb true .ieee) x)
    (hx : (((Layout.binary eb mb true .ieee).maxNorm : ℚ) : ℝ) < |x|) :
    (Layout.binary eb mb true .ieee).round m .inf x zneg =
      let L := Layout.binary eb mb true .ieee
      let top := Layout.fieldVal eb mb L.topField (decide (x < 0))
      match m with
      | .rn => if |x| < (((Layout.magnitude eb mb L.topField : ℚ) : ℝ) +
            ((Layout.magnitude eb mb (L.topField + 1) : ℚ) : ℝ)) / 2 then some top
        else some (.inf (decide (x < 0)))
      | .rz => some top
      | .rm => if decide (x < 0) then some (.inf true) else some top
      | .rp => if decide (x < 0) then some top else some (.inf false)
      | .rs .. => none := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx
    have := Layout.mag_le_maxNorm (eb := eb) (mb := mb) (signed := true) (sp := .ieee)
      (F := 0) (Nat.zero_le _)
    rw [Layout.magnitude_zero] at this; push_cast at this; linarith
  simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, hx, and_self]
  cases m <;> simp only [] <;> split_ifs <;> simp_all

/-- An unsigned layout has no result below its smallest positive value. -/
theorem Layout.round_unsigned_below {eb mb : Nat} {sp : Specials} {m : RoundMode}
    {ov : Overflow} {x : ℝ} {zneg : Bool}
    (hx : x < ((Layout.magnitude eb mb 1 : ℚ) : ℝ))
    (hmax : |x| ≤ (((Layout.binary eb mb false sp).maxNorm : ℚ) : ℝ)) :
    (Layout.binary eb mb false sp).round m ov x zneg = none := by
  by_cases hm : m.applies (.binary eb mb false sp) x
  · by_cases hx0 : x = 0
    · simp [Layout.round, hx0]
    · simp only [Layout.round, hm, not_true_eq_false, ↓reduceIte, hx0, not_lt.mpr hmax, hx,
        and_self]
  · simp only [Layout.round, hm, not_false_eq_true, ↓reduceIte]


theorem RoundMode.away_rz (neg : Bool) (a t u : ℝ) (e : Option Bool) :
    RoundMode.rz.away neg a t u e = some false := rfl

theorem RoundMode.away_rm (neg : Bool) (a t u : ℝ) (e : Option Bool) :
    RoundMode.rm.away neg a t u e = some neg := rfl

theorem RoundMode.away_rp (neg : Bool) (a t u : ℝ) (e : Option Bool) :
    RoundMode.rp.away neg a t u e = some !neg := rfl

/-- `.rn` below the midpoint stays at the neighbour nearer to zero. -/
theorem RoundMode.away_rn_lt {neg : Bool} {a t u : ℝ} {e : Option Bool} (h : a - t < u - a) :
    RoundMode.rn.away neg a t u e = some false := by
  simp [RoundMode.away, h]

/-- `.rn` above the midpoint goes away from zero. -/
theorem RoundMode.away_rn_gt {neg : Bool} {a t u : ℝ} {e : Option Bool} (h : u - a < a - t) :
    RoundMode.rn.away neg a t u e = some true := by
  simp [RoundMode.away, h, not_lt.mpr h.le]

/-- `.rn` at the midpoint goes to the even code. -/
theorem RoundMode.away_rn_tie {neg : Bool} {a t u : ℝ} {e : Option Bool} (h : a - t = u - a) :
    RoundMode.rn.away neg a t u e = e.map (!·) := by
  simp [RoundMode.away, h]

/-- `.rs k r` with `D` discarded units goes away from zero when `D + r` carries out of `k` bits. -/
theorem RoundMode.away_rs {k r D : Nat} {neg : Bool} {a t u : ℝ} {e : Option Bool}
    (htu : t < u) (hD : (a - t) * 2 ^ k = D * (u - t)) :
    (RoundMode.rs k r).away neg a t u e =
      some (decide ((2 : ℝ) ^ k ≤ (D : ℝ) + (r : ℝ))) := by
  have hne : u - t ≠ 0 := by linarith
  have hq : (a - t) * 2 ^ k / (u - t) = D := by rw [hD]; field_simp
  have hex : ∃ D' : ℕ, (a - t) * 2 ^ k = D' * (u - t) := ⟨D, hD⟩
  simp only [RoundMode.away, hex, ↓reduceIte, hq]

theorem Layout.maxNorm_fixed (w frac : Nat) :
    (Layout.fixed w frac).maxNorm = ((2 ^ (w - 1) - 1 : ℕ) : ℚ) * (2 : ℚ) ^ (-(frac : ℤ)) := rfl

theorem Layout.maxNorm_fixed_nonneg (w frac : Nat) :
    (0 : ℝ) ≤ (((Layout.fixed w frac).maxNorm : ℚ) : ℝ) := by
  have : (0 : ℚ) ≤ (Layout.fixed w frac).maxNorm := by
    rw [Layout.maxNorm_fixed]
    exact mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (by norm_num) _)
  exact_mod_cast this

/-- `.rs` has no result on a fixed-point layout. -/
theorem Layout.round_fixed_rs (w frac k r : Nat) (ov : Overflow) (x : ℝ) (zneg : Bool) :
    (Layout.fixed w frac).round (.rs k r) ov x zneg = none := rfl

/-- An exact zero is the one zero `+0` of a fixed-point layout. -/
theorem Layout.round_fixed_zero {w frac : Nat} {m : RoundMode} {ov : Overflow} {zneg : Bool}
    (hm : ∀ k r, m ≠ .rs k r) : (Layout.fixed w frac).round m ov 0 zneg = some (.zero false) := by
  cases m <;> first | exact absurd rfl (hm _ _) | simp [Layout.round]

/-- Above MAX_NORM a fixed-point layout saturates under `.satfinite` and has no result
otherwise. -/
theorem Layout.round_fixed_over {w frac : Nat} {m : RoundMode} {ov : Overflow} {x : ℝ}
    {zneg : Bool} (hm : ∀ k r, m ≠ .rs k r)
    (hx : (((Layout.fixed w frac).maxNorm : ℚ) : ℝ) < x) :
    (Layout.fixed w frac).round m ov x zneg =
      if ov = .satfinite then some (.fin (Layout.fixed w frac).maxNorm) else none := by
  have h0 := Layout.maxNorm_fixed_nonneg w frac
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; linarith
  have hpos : 0 < x := by linarith
  have ha : (((Layout.fixed w frac).maxNorm : ℚ) : ℝ) < |x| := by rwa [abs_of_pos hpos]
  cases m <;> first | exact absurd rfl (hm _ _) |
    simp only [Layout.round, hx0, ha, hpos, and_true, ↓reduceIte]

/-- Below the negative of MAX_NORM a fixed-point layout has no result: the sign-preserved
MAX_NORM of `.satfinite` reads as `-MAX_NORM` or as the negative maximum. -/
theorem Layout.round_fixed_under {w frac : Nat} {m : RoundMode} {ov : Overflow} {x : ℝ}
    {zneg : Bool} (hx : x < -(((Layout.fixed w frac).maxNorm : ℚ) : ℝ)) :
    (Layout.fixed w frac).round m ov x zneg = none := by
  have h0 := Layout.maxNorm_fixed_nonneg w frac
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; linarith
  have hneg : ¬ 0 < x := by intro h; linarith
  have ha : (((Layout.fixed w frac).maxNorm : ℚ) : ℝ) < |x| := by
    rw [abs_of_neg (by linarith)]; linarith
  cases m <;> simp only [Layout.round, hx0, ha, hneg, and_false, ↓reduceIte]

/-- A value of a fixed-point layout, the integer `k` times `2^-frac` with a sign, rounds to
itself. -/
theorem Layout.round_fixed_exact {w frac : Nat} {m : RoundMode} {ov : Overflow} {x : ℝ}
    {zneg : Bool} {k : Nat} (hm : ∀ k r, m ≠ .rs k r) (hx0 : x ≠ 0)
    (hk : |x| * 2 ^ frac = k) (hx : |x| ≤ (((Layout.fixed w frac).maxNorm : ℚ) : ℝ)) :
    (Layout.fixed w frac).round m ov x zneg = some (Layout.fixedVal frac k (decide (x < 0))) := by
  have hfl : ⌊|x| * 2 ^ frac⌋.toNat = k := by rw [hk]; simp
  cases m <;> first | exact absurd rfl (hm _ _) |
    (simp only [Layout.round, hx0, not_lt.mpr hx, hfl, ↓reduceIte]; simp only [hk, ↓reduceIte])

/-- A number strictly between the consecutive values `k * 2^-frac` and `(k + 1) * 2^-frac` of a
fixed-point layout rounds to one of them as `RoundMode.away` decides. -/
theorem Layout.round_fixed_between {w frac : Nat} {m : RoundMode} {ov : Overflow} {x : ℝ}
    {zneg : Bool} {k : Nat} (hm : ∀ k r, m ≠ .rs k r)
    (h1 : (k : ℝ) < |x| * 2 ^ frac) (h2 : |x| * 2 ^ frac < k + 1)
    (hx : |x| ≤ (((Layout.fixed w frac).maxNorm : ℚ) : ℝ)) :
    (Layout.fixed w frac).round m ov x zneg =
      (m.away (decide (x < 0)) |x| ((k : ℝ) / 2 ^ frac) (((k : ℝ) + 1) / 2 ^ frac)
        (some (k % 2 == 0))).map
        fun up => Layout.fixedVal frac (if up then k + 1 else k) (decide (x < 0)) := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero, zero_mul] at h1; exact absurd h1 (not_lt.mpr (Nat.cast_nonneg k))
  have hfl : ⌊|x| * 2 ^ frac⌋.toNat = k := by
    have : ⌊|x| * 2 ^ frac⌋ = (k : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨h1.le, h2⟩
    rw [this]; simp
  have hne : ¬ ((k : ℝ) = |x| * 2 ^ frac) := ne_of_lt h1
  cases m <;> first | exact absurd rfl (hm _ _) |
    simp only [Layout.round, hx0, not_lt.mpr hx, hfl, hne, ↓reduceIte]


/-- The overflow policy of the bits of a payload (EXT-FLOAT-BITS): IEEE 754 overflow for `.f64`,
`.f32`, `.f16` and `.bf16`, saturation to MAX_NORM for `.e4m3` and `.e5m2`. -/
def FloatFmt.overflow : FloatFmt → Overflow
  | .e4m3 | .e5m2 => .satfinite
  | _ => .inf

/-- The largest magnitude field a rounded payload takes: the infinity field of an IEEE format,
the MAX_NORM field of a saturating 8-bit format. -/
def FloatFmt.maxField : FloatFmt → Nat
  | .e4m3 => 0x7E
  | .e5m2 => 0x7B
  | fmt => (2 ^ fmt.expBits - 1) * 2 ^ fmt.mantBits

/-- The `fmt` pattern of the number `x` (EXT-FLOAT-BITS): `x` rounded to nearest, ties to even,
with the format's overflow policy, and zero as `+0`. -/
def FloatFmt.encode (fmt : FloatFmt) (x : ℝ) : Nat :=
  ((fmt.layout.round .rn fmt.overflow x false).bind fmt.layout.encode).getD 0

/-- The facts of the payload layouts that `FloatFmt.encode_eq` uses. -/
theorem FloatFmt.layout_facts (fmt : FloatFmt) :
    0 < fmt.layout.topField ∧ fmt.layout.topField < 2 ^ (fmt.expBits + fmt.mantBits) ∧
    fmt.mantBits ≠ 0 ∧ fmt.layout.width = fmt.expBits + fmt.mantBits + 1 ∧
    fmt.layout.topField ≤ fmt.maxField ∧
    (fmt.overflow = .satfinite → fmt.maxField = fmt.layout.topField) ∧
    (fmt.overflow = .inf → fmt ≠ .e4m3 ∧ fmt.maxField = fmt.layout.topField + 1 ∧
      fmt.layout.topField % 2 = 1 ∧ fmt.layout.topField + 1 < 2 ^ (fmt.expBits + fmt.mantBits) ∧
      fmt.layout.topField + 1 = (2 ^ fmt.expBits - 1) * 2 ^ fmt.mantBits) := by
  cases fmt <;> decide

/-- The pattern of a field up to `topField` of a payload format. -/
theorem FloatFmt.encode_fieldVal (fmt : FloatFmt) {F : Nat} (neg : Bool)
    (hF : F ≤ fmt.layout.topField) :
    fmt.layout.encode (Layout.fieldVal fmt.expBits fmt.mantBits F neg) =
      some ((if neg then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F) := by
  obtain ⟨-, htop, -, hw, -⟩ := FloatFmt.layout_facts fmt
  apply Layout.encode_decode _ (FloatFmt.decode_field fmt neg hF)
  rw [hw, Nat.pow_succ]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

open Classical in
/-- Today's definition of the bits of a payload as a theorem: the largest field `lo` up to
`maxField` whose magnitude is at most `|x|`, or the next field above the midpoint or at it with
`lo` odd, with the sign bit of `x`. -/
theorem FloatFmt.encode_eq (fmt : FloatFmt) (x : ℝ) : fmt.encode x =
    let lo := Nat.findGreatest (fun F => (fmt.magnitude F : ℝ) ≤ |x|) fmt.maxField
    let mid : ℝ := ((fmt.magnitude lo + fmt.magnitude (lo + 1)) / 2 : ℚ)
    (if x < 0 then 2 ^ (fmt.expBits + fmt.mantBits) else 0) +
      (if lo < fmt.maxField ∧ (mid < |x| ∨ (mid = |x| ∧ lo % 2 = 1)) then lo + 1 else lo) := by
  obtain ⟨htop0, -, hmb, -, hmax, hsat, hinf⟩ := FloatFmt.layout_facts fmt
  have hencF : ∀ (F : ℕ) (neg : Bool), F ≤ fmt.layout.topField →
      fmt.layout.encode (Layout.fieldVal fmt.expBits fmt.mantBits F neg) =
        some ((if neg then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F) :=
    fun _ neg h => FloatFmt.encode_fieldVal fmt neg h
  have hL := FloatFmt.layout_eq fmt
  dsimp only
  unfold FloatFmt.encode
  delta FloatFmt.magnitude
  generalize fmt.maxField = B at hmax hsat hinf
  generalize hT : fmt.layout.topField = T at htop0 hmax hsat hinf hencF
  have hT' : (Layout.binary fmt.expBits fmt.mantBits true
      (if fmt = .e4m3 then .e4m3 else .ieee)).topField = T := by rw [← hL]; exact hT
  have hmaxN : (Layout.binary fmt.expBits fmt.mantBits true
      (if fmt = .e4m3 then .e4m3 else .ieee)).maxNorm = Layout.magnitude fmt.expBits
        fmt.mantBits T := by rw [Layout.maxNorm_binary, hT']
  rw [hL]
  rw [hL] at hencF
  clear hL hT
  set E := fmt.expBits with hE
  set M := fmt.mantBits with hM
  set sp := (if fmt = .e4m3 then Specials.e4m3 else .ieee) with hsp
  have hmono : ∀ {F G : ℕ}, F < G →
      ((Layout.magnitude E M F : ℚ) : ℝ) < ((Layout.magnitude E M G : ℚ) : ℝ) := fun h => by
    exact_mod_cast Layout.magnitude_strictMono E M h
  have hmag0 : ((Layout.magnitude E M 0 : ℚ) : ℝ) = 0 := by simp [Layout.magnitude_zero]
  have hmaxR : (((Layout.binary E M true sp).maxNorm : ℚ) : ℝ) =
      ((Layout.magnitude E M T : ℚ) : ℝ) := by rw [hmaxN]
  have hsgn : ∀ F, (if decide (x < 0) = true then 2 ^ (E + M) else 0) + F =
      (if x < 0 then 2 ^ (E + M) else 0) + F := by intro F; simp
  have hmidR : ∀ F : ℕ, (((Layout.magnitude E M F + Layout.magnitude E M (F + 1)) / 2 : ℚ) : ℝ) =
      (((Layout.magnitude E M F : ℚ) : ℝ) + ((Layout.magnitude E M (F + 1) : ℚ) : ℝ)) / 2 := by
    intro F; push_cast; ring
  have hfin : ∀ neg : Bool, FVal.fin (if neg && true then -(Layout.binary E M true sp).maxNorm
      else (Layout.binary E M true sp).maxNorm) = Layout.fieldVal E M T neg := by
    intro neg
    simp only [Bool.and_true, hmaxN, Layout.fieldVal, Nat.pos_iff_ne_zero.mp htop0, ↓reduceIte]
  simp only [hmidR]
  by_cases hx0 : x = 0
  · subst hx0
    rw [Layout.round_zero (m := .rn) trivial]
    have h0 := hencF 0 false (Nat.zero_le _)
    simp only [Layout.fieldVal, ↓reduceIte] at h0
    have hlo : Nat.findGreatest (fun F => ((Layout.magnitude E M F : ℚ) : ℝ) ≤ |(0 : ℝ)|) B = 0 :=
      Layout.findGreatest_mag (Nat.zero_le _) (by simp [hmag0])
        (by rw [abs_zero, ← hmag0]; exact hmono Nat.zero_lt_one)
    have h1 := hmono (F := 0) (G := 1) Nat.zero_lt_one
    rw [hmag0] at h1
    simp only [Option.bind_some, h0, Option.getD_some]
    rw [hlo]
    have hq0 : Layout.magnitude E M 0 = 0 := Layout.magnitude_zero E M
    have hq1 : (0 : ℚ) < Layout.magnitude E M 1 := Layout.magnitude_pos Nat.zero_lt_one
    simp only [lt_irrefl, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]
    split_ifs
    all_goals first
      | rfl
      | (exfalso
         rename_i hc
         rcases hc with ⟨-, hc | ⟨-, hc⟩⟩
         · rw [hmag0, abs_zero] at hc; linarith
         · simp at hc)
  have hneg : decide (x < 0) = decide (x < 0) := rfl
  by_cases hbig : (((Layout.binary E M true sp).maxNorm : ℚ) : ℝ) < |x|
  · rw [hmaxR] at hbig
    cases hov : fmt.overflow
    · obtain ⟨hne4, hB, hodd, hlt, hinfF⟩ := hinf hov
      have hspi : sp = .ieee := by simp [hsp, hne4]
      rw [hspi] at hmaxR hencF ⊢
      have hrw : (Layout.binary E M true .ieee).topField = T := by rw [← hspi]; exact hT'
      rw [Layout.round_inf_ieee (m := .rn) trivial (by rw [hmaxR]; exact hbig)]
      simp only [hrw]
      have hinfE : (Layout.binary E M true .ieee).encode (.inf (decide (x < 0))) =
          some ((if decide (x < 0) then 2 ^ (E + M) else 0) + (T + 1)) := by
        have hp : (Layout.binary E M true .ieee).infPattern (decide (x < 0)) =
            (if decide (x < 0) then 2 ^ (E + M) else 0) + (T + 1) := by
          simp only [Layout.infPattern, hinfF]
        rw [← hp]
        refine Layout.encode_decode ?_ (Layout.decode_infPattern_ieee (by simp))
        rw [hp]
        simp only [Layout.width, ↓reduceIte, Nat.pow_succ]
        cases decide (x < 0) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      subst hB
      have hmid : (((Layout.magnitude E M T : ℚ) : ℝ) +
          ((Layout.magnitude E M (T + 1) : ℚ) : ℝ)) / 2 < ((Layout.magnitude E M (T + 1) : ℚ) : ℝ)
          := by have := hmono (Nat.lt_succ_self T); linarith
      by_cases hge : ((Layout.magnitude E M (T + 1) : ℚ) : ℝ) ≤ |x|
      · rw [Nat.findGreatest_eq hge]
        simp only [not_lt.mpr (le_trans hmid.le hge), ↓reduceIte, Option.bind_some, hinfE,
          Option.getD_some, lt_irrefl, false_and, hsgn]
      · have hlo := Layout.findGreatest_mag (eb := E) (mb := M) (a := |x|) (Nat.le_succ T)
          hbig.le (lt_of_not_ge hge)
        rw [hlo]
        by_cases hm : |x| < (((Layout.magnitude E M T : ℚ) : ℝ) +
            ((Layout.magnitude E M (T + 1) : ℚ) : ℝ)) / 2
        · simp only [hm, ↓reduceIte, Option.bind_some, hencF T _ le_rfl, Option.getD_some, hsgn]
          congr 1
          split_ifs with hc
          · exfalso; obtain ⟨-, hc | ⟨hc, -⟩⟩ := hc <;> linarith
          · rfl
        · simp only [hm, ↓reduceIte, Option.bind_some, hinfE, Option.getD_some, hsgn]
          congr 1
          split_ifs with hc
          · rfl
          · exfalso; apply hc; refine ⟨Nat.lt_succ_self T, ?_⟩
            rcases lt_or_eq_of_le (not_lt.mp hm) with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, hodd⟩
    · have hB := hsat hov
      subst hB
      rw [Layout.round_satfinite (m := .rn) trivial (by rw [hmaxR]; exact hbig), hfin]
      rw [Nat.findGreatest_eq hbig.le]
      simp only [Option.bind_some, hencF B _ le_rfl, Option.getD_some, lt_irrefl, false_and,
        ↓reduceIte, hsgn]
  · rw [hmaxR, not_lt] at hbig
    have hP0 : ((Layout.magnitude E M 0 : ℚ) : ℝ) ≤ |x| := by rw [hmag0]; exact abs_nonneg x
    set F := Nat.findGreatest (fun F => ((Layout.magnitude E M F : ℚ) : ℝ) ≤ |x|) T with hFdef
    have hF1 : ((Layout.magnitude E M F : ℚ) : ℝ) ≤ |x| :=
      Nat.findGreatest_spec (P := fun F => ((Layout.magnitude E M F : ℚ) : ℝ) ≤ |x|)
        (Nat.zero_le T) hP0
    have hFT : F ≤ T := Nat.findGreatest_le T
    have hF2 : |x| < ((Layout.magnitude E M (F + 1) : ℚ) : ℝ) := by
      by_cases h : F < T
      · exact lt_of_not_ge (Nat.findGreatest_is_greatest (Nat.lt_succ_self F) h)
      · have : F = T := by omega
        rw [this]; exact lt_of_le_of_lt hbig (hmono (Nat.lt_succ_self T))
    have hlo := Layout.findGreatest_mag (eb := E) (mb := M) (hFT.trans hmax) hF1 hF2
    rw [hlo]
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    have hmid1 : ((Layout.magnitude E M F : ℚ) : ℝ) < ((Layout.magnitude E M (F + 1) : ℚ) : ℝ) :=
      hmono (Nat.lt_succ_self F)
    by_cases hex : ((Layout.magnitude E M F : ℚ) : ℝ) = |x|
    · have hF0 : 0 < F := by
        rcases Nat.eq_zero_or_pos F with h | h
        · rw [h, hmag0] at hex; linarith
        · exact h
      rw [Layout.round_exact (m := .rn) trivial hF0 (hT' ▸ hFT) hex.symm (by simp)]
      simp only [Option.bind_some, hencF F _ hFT, Option.getD_some, hsgn]
      congr 1
      split_ifs with hc
      · exfalso; obtain ⟨-, hc | ⟨hc, -⟩⟩ := hc <;> linarith
      · rfl
    · have hlt : ((Layout.magnitude E M F : ℚ) : ℝ) < |x| := lt_of_le_of_ne hF1 hex
      have hFT' : F < T := by
        rcases lt_or_eq_of_le hFT with h | h
        · exact h
        · rw [h] at hlt; linarith
      rw [Layout.round_between (m := .rn) trivial (hT' ▸ hFT') hlt hF2 (by simp)]
      simp only [hmb, ↓reduceIte]
      rcases lt_trichotomy (|x| - ((Layout.magnitude E M F : ℚ) : ℝ))
        (((Layout.magnitude E M (F + 1) : ℚ) : ℝ) - |x|) with h | h | h
      · rw [RoundMode.away_rn_lt h]
        simp only [Option.map_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
          hencF F _ hFT, Option.getD_some, hsgn]
        congr 1
        split_ifs with hc
        · exfalso; obtain ⟨-, hc | ⟨hc, -⟩⟩ := hc <;> linarith
        · rfl
      · rw [RoundMode.away_rn_tie h]
        rcases Nat.mod_two_eq_zero_or_one F with he | he
        · simp only [(show (F % 2 == 0) = true by simp [he]), Option.map_some, Bool.not_true,
            Bool.false_eq_true,
            ↓reduceIte, Option.bind_some, hencF F _ hFT, Option.getD_some, hsgn]
          congr 1
          split_ifs with hc
          · exfalso; obtain ⟨-, hc | ⟨-, hc⟩⟩ := hc
            · linarith
            · omega
          · rfl
        · simp only [(show (F % 2 == 0) = false by simp [he]), Option.map_some, Bool.not_false,
            ↓reduceIte,
            Option.bind_some, hencF (F + 1) _ hFT', Option.getD_some, hsgn]
          congr 1
          split_ifs with hc
          · rfl
          · exfalso; apply hc; exact ⟨by omega, Or.inr ⟨by linarith, he⟩⟩
      · rw [RoundMode.away_rn_gt h]
        simp only [Option.map_some, ↓reduceIte, Option.bind_some, hencF (F + 1) _ hFT',
          Option.getD_some, hsgn]
        congr 1
        split_ifs with hc
        · rfl
        · exfalso; apply hc; exact ⟨by omega, Or.inl (by linarith)⟩

/-- A pattern of a payload format whose datum is a number is the field of its low bits, at most
`topField`, with its sign bit. -/
theorem FloatFmt.decode_number (fmt : FloatFmt) {n : Nat} {v : FVal}
    (h : fmt.layout.decode n = some v) (hv : v.num ≠ none) :
    v = Layout.fieldVal fmt.expBits fmt.mantBits (n % 2 ^ (fmt.expBits + fmt.mantBits))
      (n / 2 ^ (fmt.expBits + fmt.mantBits) % 2 == 1) ∧
    n % 2 ^ (fmt.expBits + fmt.mantBits) ≤ fmt.layout.topField := by
  have hL := FloatFmt.layout_eq fmt
  rw [hL] at h ⊢
  rcases Layout.decode_binary_cases h with h1 | h1 | ⟨h1, -⟩
  · subst h1; simp [FVal.num] at hv
  · refine ⟨by simpa using h1, ?_⟩
    have hlow := Layout.binary_low fmt.expBits fmt.mantBits true
      (if fmt = .e4m3 then .e4m3 else .ieee) n
    have hk := Nat.mod_lt n (Nat.two_pow_pos (fmt.expBits + fmt.mantBits))
    simp only [Layout.decode, hlow] at h
    generalize n % 2 ^ (fmt.expBits + fmt.mantBits) = F at h h1 hk ⊢
    generalize (true && n % 2 ^ (Layout.binary fmt.expBits fmt.mantBits true
      (if fmt = .e4m3 then .e4m3 else .ieee)).width / 2 ^ (fmt.expBits + fmt.mantBits) % 2 == 1)
      = s at h
    generalize hw : (n / 2 ^ (fmt.expBits + fmt.mantBits) % 2 == 1) = s' at h1
    cases fmt <;>
      simp only [FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.layout, Layout.topField,
        reduceCtorEq, ↓reduceIte, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]
        at h h1 hk ⊢ <;>
      split_ifs at h <;>
      first
        | omega
        | (exfalso; cases h; exact Layout.fieldVal_ne_inf _ _ _ _ _ h1.symm)
        | (exfalso; cases h; exact Layout.fieldVal_ne_nan _ _ _ _ _ h1.symm)
  · subst h1; simp [FVal.num] at hv

/-- The payload of a number decoded from a pattern has the pattern's datum as its bits, with
either zero written as `+0`. -/
theorem FloatFmt.decode_encode_of_decode (fmt : FloatFmt) {n : Nat} {q : ℚ}
    (h : fmt.decode n = some q) : fmt.layout.decode (fmt.encode q) = some (FVal.ofRat q) := by
  unfold FloatFmt.decode at h
  obtain ⟨v, hv, hq⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hvF, hF⟩ := FloatFmt.decode_number fmt hv (by rw [hq]; simp)
  generalize n % 2 ^ (fmt.expBits + fmt.mantBits) = F at hvF hF
  generalize (n / 2 ^ (fmt.expBits + fmt.mantBits) % 2 == 1) = s at hvF
  subst hvF
  rw [FVal.num_fieldVal] at hq
  injection hq with hq
  have hL := FloatFmt.layout_eq fmt
  have hF' : F ≤ (Layout.binary fmt.expBits fmt.mantBits true
      (if fmt = .e4m3 then .e4m3 else .ieee)).topField := by rw [← hL]; exact hF
  rcases Nat.eq_zero_or_pos F with h0 | h0
  · subst h0
    have hq0 : q = 0 := by rw [← hq, Layout.magnitude_zero]; simp
    subst hq0
    have hr : fmt.layout.round .rn fmt.overflow (0 : ℝ) false = some (.zero false) := by
      rw [hL]; exact Layout.round_zero (m := .rn) trivial
    have he := FloatFmt.encode_fieldVal fmt false (Nat.zero_le fmt.layout.topField)
    have hd := FloatFmt.decode_field fmt false (Nat.zero_le fmt.layout.topField)
    simp only [Layout.fieldVal, ↓reduceIte] at he hd
    unfold FloatFmt.encode
    rw [Rat.cast_zero, hr]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at he hd
    simp [he, hd, FVal.ofRat]
  · have hpos := Layout.magnitude_pos (eb := fmt.expBits) (mb := fmt.mantBits) h0
    have hs : decide (((q : ℚ) : ℝ) < 0) = s := by
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at hq <;> rw [← hq] <;>
        simp [hpos.le, hpos]
    have hab : |((q : ℚ) : ℝ)| = ((Layout.magnitude fmt.expBits fmt.mantBits F : ℚ) : ℝ) := by
      rw [← hq]; cases s <;> simp [Layout.magnitude_nonneg]
    have hr : fmt.layout.round .rn fmt.overflow ((q : ℚ) : ℝ) false =
        some (Layout.fieldVal fmt.expBits fmt.mantBits F s) := by
      rw [hL, ← hs]; exact Layout.round_exact (m := .rn) trivial h0 hF' hab (by simp)
    have hq0 : q ≠ 0 := by rw [← hq]; cases s <;> simp [hpos.ne']
    unfold FloatFmt.encode
    rw [hr]
    simp only [Option.bind_some, FloatFmt.encode_fieldVal fmt s hF, Option.getD_some,
      FloatFmt.decode_field fmt s hF]
    simp only [Layout.fieldVal, h0.ne', ↓reduceIte, FVal.ofRat, hq0, hq]

/-- A representable number has its own datum as its bits (`+0` for `0`). -/
theorem FloatFmt.decode_encode {fmt : FloatFmt} {x : ℝ} (h : fmt.representable x) :
    ∃ q : ℚ, (q : ℝ) = x ∧ fmt.layout.decode (fmt.encode x) = some (FVal.ofRat q) := by
  obtain ⟨n, q, hn, hq⟩ := h
  exact ⟨q, hq, hq ▸ FloatFmt.decode_encode_of_decode fmt hn⟩

end

end PTX
