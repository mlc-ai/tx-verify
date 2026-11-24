-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Isa.Types
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Floating-point and fixed-point formats

The layout of every floating and fixed-point data format, and the floating datum a pattern of a
layout denotes.
-/

namespace PTX

/-! ## THREAD-FLOAT-FORMAT — floating and fixed-point layouts
Statement: A floating datum is a zero with a sign, a finite nonzero number, an infinity with a
  sign, or NaN, with its pattern when the pattern is known. A binary layout reads a pattern as a
  sign bit, an exponent field and a mantissa field, with subnormal numbers at the zero exponent
  field, and gives each format's encodings of infinity and NaN. The fixed-point layout of `.s2f6`
  reads a pattern as a two's complement integer times `2^-6`.

Defs: FVal, FVal.num, FVal.ofRat, Specials, Layout, Layout.width, Layout.bias, Layout.magnitude,
  Layout.fieldVal, Layout.decode, Layout.encode, Layout.minNormal, Layout.topField, Layout.maxNorm,
  Layout.subnormal, Layout.flush, Layout.signPattern, Layout.infPattern, FloatFmt.layout,
  FType.layout?, FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.magnitude,
  FloatFmt.decode, f32Value, FloatFmt.representable, Layout.magnitude_zero,
  Layout.magnitude_lt_succ, Layout.magnitude_strictMono, Layout.magnitude_pos,
  Layout.magnitude_nonneg, Layout.fieldVal_inj, Layout.binary_low, Layout.binary_sign,
  Layout.binary_pattern, Layout.decode_binary_cases, Layout.fieldVal_ne_nan, Layout.fieldVal_ne_inf,
  Layout.decode_binary_inj, Layout.decode_fixed_inj, Layout.decode_inj, Layout.encode_decode,
  Layout.decode_of_encode, FVal.num_fieldVal, FloatFmt.layout_eq, FloatFmt.magnitude_eq,
  FloatFmt.decode_eq, Layout.binary_pattern_parts, Layout.decode_field_ieee,
  Layout.decode_field_e4m3, Layout.decode_infPattern_ieee, FloatFmt.decode_field,
  FloatFmt.decode_signPattern, FloatFmt.decode_infPattern

Source:
- §5.2.3: "the .f16 type indicates 5 bits reserved for exponent and 10 bits reserved for mantissa"
- §5.2.3: "bf16 data format: This data format is a 16-bit floating point format with 8 bits for
    exponent and 7 bits for mantissa."
- §5.2.3: "e5m2 data format: This data format is an 8-bit floating point format with 5 bits for
    exponent and 2 bits for mantissa"
- §5.2.3: "The e4m3 encoding does not support infinity and NaN values are limited to 0x7f and 0xff"
- §4.5.2: "To specify IEEE 754 double-precision floating point values, the constant begins with 0d
    or 0D followed by 16 hex digits."
- §5.2.3: "The ue8m0 encoding does not support infinity. NaN value is limited to 0xff ."
- §5.2.4: "This data format is 8-bit signed 2’s complement integer with 2 sign-integer bits and 6
    fractional bits with form xx.xxxxxx ."
- §5.2.4: "The s2f6 encoding does not support infinity and NaN ."
- §5.2.4: "s2f6 value = s8 value * 2^(-6)"
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- EXT-UE8M0
- EXT-NARROW-FLOAT

Direction: representation

Applies: The patterns of every floating and fixed-point format

Premises: None.

Effect: Representation. `.f64`, `.f32`, `.f16`, `.bf16` and `.e5m2` are IEEE 754 binary layouts
  with infinities and NaN at the all-ones exponent field; `.e4m3` has no infinity and its NaN is
  the pattern with exponent and mantissa all ones; `.ue8m0` and `.ue5m3` have no sign bit, no
  infinity, and NaN at the all-ones pattern, and the `.ue8m0` pattern `0` has no value
  (EXT-UE8M0); `.e2m1`, `.e2m3` and `.e3m2` have neither infinity nor NaN (EXT-NARROW-FLOAT).
  `.tf32` has no layout, since its internal layout is implementation defined. A NaN read from a
  pattern keeps the pattern. `Layout.encode` is the inverse of `Layout.decode`. The format `.f64`
  is the IEEE 754 double-precision format, with 11 exponent bits and 52 mantissa bits (§4.5.2).
  `FloatFmt.decode` and `f32Value` give the number of a finite pattern of a payload format, with
  either zero read as `0`. `Layout.maxNorm` is the largest finite magnitude (MAX_NORM), and
  `Layout.flush` maps a subnormal number to the zero of its sign, as `.ftz` does.
-/

/-- A floating datum as IEEE 754 classifies it: a zero with its sign, a finite nonzero number, an
infinity with its sign, or NaN with its pattern when the pattern is known. -/
inductive FVal where
  | zero (neg : Bool)
  | fin (x : ℚ)
  | inf (neg : Bool)
  | nan (bits : Option Nat)
  deriving DecidableEq, Repr

/-- The number of a finite datum, with either zero read as `0`; `none` for an infinity and NaN. -/
def FVal.num : FVal → Option ℚ
  | .zero _ => some 0
  | .fin x => some x
  | _ => none

/-- The datum of the number `q`: `+0` for `0`, and `.fin q` otherwise. -/
def FVal.ofRat (q : ℚ) : FVal := if q = 0 then .zero false else .fin q

/-- How a binary layout encodes infinity and NaN, and which pattern has no value. -/
inductive Specials where
  /-- IEEE 754: the all-ones exponent field is an infinity (zero mantissa) or NaN. -/
  | ieee
  /-- `.e4m3`: exponent and mantissa all ones is NaN; there is no infinity. -/
  | e4m3
  /-- The all-ones pattern is NaN; there is no infinity (`.ue5m3`). -/
  | allOnesNaN
  /-- `.ue8m0` (EXT-UE8M0): the all-ones pattern is NaN and the pattern `0` has no value. -/
  | ue8m0
  /-- Neither infinity nor NaN (`.e2m1`, `.e2m3`, `.e3m2`). -/
  | none
  deriving DecidableEq, Repr

/-- A data layout: a binary floating layout with `eb` exponent and `mb` mantissa bits, a sign
bit above them when `signed`, and its special encodings; or a two's complement fixed-point layout
of `w` bits with `frac` fraction bits. -/
inductive Layout where
  | binary (eb mb : Nat) (signed : Bool) (sp : Specials)
  | fixed (w frac : Nat)
  deriving DecidableEq, Repr

/-- The number of bits of a pattern. -/
def Layout.width : Layout → Nat
  | .binary eb mb signed _ => eb + mb + (if signed then 1 else 0)
  | .fixed w _ => w

/-- The exponent bias `2^(eb-1) - 1` of a binary layout. -/
def Layout.bias (eb : Nat) : ℤ := 2 ^ (eb - 1) - 1

/-- The magnitude of the exponent-and-mantissa field `F` of a binary layout: subnormal when the
exponent field is zero. -/
def Layout.magnitude (eb mb F : Nat) : ℚ :=
  let e := F / 2 ^ mb
  let m := F % 2 ^ mb
  if e = 0 then (m : ℚ) * (2 : ℚ) ^ (1 - Layout.bias eb - mb)
  else ((2 ^ mb + m : ℕ) : ℚ) * (2 : ℚ) ^ ((e : ℤ) - Layout.bias eb - mb)

/-- The datum of the magnitude field `F` of a binary layout with the sign `neg`: the zero of that
sign for the field `0`, and the signed magnitude otherwise. -/
def Layout.fieldVal (eb mb F : Nat) (neg : Bool) : FVal :=
  if F = 0 then .zero neg
  else .fin (if neg then -Layout.magnitude eb mb F else Layout.magnitude eb mb F)

/-- The datum of the low `L.width` bits of pattern `n`; `none` for a pattern without a value. -/
def Layout.decode (L : Layout) (n : Nat) : Option FVal :=
  let n := n % 2 ^ L.width
  match L with
  | .binary eb mb signed sp =>
    let F := n % 2 ^ (eb + mb)
    let neg := signed && n / 2 ^ (eb + mb) % 2 == 1
    let e := F / 2 ^ mb
    let m := F % 2 ^ mb
    let allE := e = 2 ^ eb - 1
    let number := Layout.fieldVal eb mb F neg
    match sp with
    | .ieee => if allE then (if m = 0 then some (.inf neg) else some (.nan (some n)))
      else some number
    | .e4m3 => if allE ∧ m = 2 ^ mb - 1 then some (.nan (some n)) else some number
    | .allOnesNaN => if n = 2 ^ (eb + mb) - 1 then some (.nan (some n)) else some number
    | .ue8m0 => if n = 2 ^ (eb + mb) - 1 then some (.nan (some n))
      else if n = 0 then none else some number
    | .none => some number
  | .fixed w frac =>
    let z : ℤ := if n < 2 ^ (w - 1) then n else (n : ℤ) - 2 ^ w
    if z = 0 then some (.zero false) else some (.fin ((z : ℚ) * (2 : ℚ) ^ (-(frac : ℤ))))

/-- The pattern of a datum: the least pattern that decodes to it; `none` when no pattern does (a
NaN without a known pattern, a value outside the layout). -/
def Layout.encode (L : Layout) (v : FVal) : Option Nat :=
  (List.range (2 ^ L.width)).find? fun n => L.decode n == some v

/-- The smallest positive normal magnitude of a binary layout (`2^(1-bias)`); for a fixed-point
layout, which has no subnormal numbers, `0`. -/
def Layout.minNormal : Layout → ℚ
  | .binary eb _ _ _ => (2 : ℚ) ^ (1 - Layout.bias eb)
  | .fixed .. => 0

/-- The largest finite code: for a binary layout the largest magnitude field whose pattern is a
number (below the infinity field of an IEEE layout, below the NaN field of `.e4m3`, `.ue8m0` and
`.ue5m3`, and the all-ones field of a layout without specials); for a fixed-point layout the
largest integer `2^(w-1) - 1`. -/
def Layout.topField : Layout → Nat
  | .binary eb mb _ .ieee => (2 ^ eb - 1) * 2 ^ mb - 1
  | .binary eb mb _ .none => 2 ^ (eb + mb) - 1
  | .binary eb mb _ _ => 2 ^ (eb + mb) - 2
  | .fixed w _ => 2 ^ (w - 1) - 1

/-- The largest finite magnitude MAX_NORM of a layout (`127 * 2^-6` for `.fixed 8 6`). -/
def Layout.maxNorm (L : Layout) : ℚ :=
  match L with
  | .binary eb mb _ _ => Layout.magnitude eb mb L.topField
  | .fixed _ frac => (L.topField : ℚ) * (2 : ℚ) ^ (-(frac : ℤ))

/-- Whether a number is subnormal in the layout: nonzero with magnitude below the smallest
normal magnitude. A fixed-point layout has no subnormal number. -/
def Layout.subnormal (L : Layout) (x : ℚ) : Bool := x ≠ 0 && |x| < L.minNormal

/-- The `.ftz` flush: a subnormal number becomes the zero of its sign, and every other datum is
unchanged. -/
def Layout.flush (L : Layout) : FVal → FVal
  | .fin x => if L.subnormal x then .zero (decide (x < 0)) else .fin x
  | v => v

/-- The pattern of `-0` of a signed binary layout: the sign bit alone. -/
def Layout.signPattern (L : Layout) : Nat := 2 ^ (L.width - 1)

/-- The pattern of the infinity of sign `neg` of a binary layout with IEEE specials: the
all-ones exponent field and a zero mantissa, with the sign bit when `neg`. -/
def Layout.infPattern : Layout → Bool → Nat
  | .binary eb mb _ _, neg => (if neg then 2 ^ (eb + mb) else 0) + (2 ^ eb - 1) * 2 ^ mb
  | .fixed .., _ => 0

/-- The layout of a payload format. -/
def FloatFmt.layout : FloatFmt → Layout
  | .f64 => .binary 11 52 true .ieee
  | .f32 => .binary 8 23 true .ieee
  | .f16 => .binary 5 10 true .ieee
  | .bf16 => .binary 8 7 true .ieee
  | .e4m3 => .binary 4 3 true .e4m3
  | .e5m2 => .binary 5 2 true .ieee

/-- The layout of a floating or fixed-point type; `.tf32` has none, its internal layout being
implementation defined (§5.2.3). -/
def FType.layout? : FType → Option Layout
  | .tf32 => none
  | .e2m1 => some (.binary 2 1 true .none)
  | .e2m3 => some (.binary 2 3 true .none)
  | .e3m2 => some (.binary 3 2 true .none)
  | .ue8m0 => some (.binary 8 0 false .ue8m0)
  | .ue5m3 => some (.binary 5 3 false .allOnesNaN)
  | .s2f6 => some (.fixed 8 6)
  | f => f.fmt?.map FloatFmt.layout

/-- The exponent field width of a payload format (§5.2.3), read from its layout. -/
def FloatFmt.expBits (fmt : FloatFmt) : Nat :=
  match fmt.layout with
  | .binary eb .. => eb
  | .fixed .. => 0

/-- The mantissa field width of a payload format (§5.2.3), read from its layout. -/
def FloatFmt.mantBits (fmt : FloatFmt) : Nat :=
  match fmt.layout with
  | .binary _ mb .. => mb
  | .fixed .. => 0

/-- The exponent bias `2^(expBits-1) - 1` of a payload format. -/
def FloatFmt.bias (fmt : FloatFmt) : Nat := 2 ^ (fmt.expBits - 1) - 1

/-- The magnitude of the exponent-and-mantissa field `F` of a payload format (sign excluded). -/
def FloatFmt.magnitude (fmt : FloatFmt) (F : Nat) : ℚ :=
  Layout.magnitude fmt.expBits fmt.mantBits F

/-- The number of a finite `fmt` pattern (the low `8 * fmt.bytes` bits of `n`), with either zero
read as `0`; `none` for NaN and infinities. -/
def FloatFmt.decode (fmt : FloatFmt) (n : Nat) : Option ℚ :=
  (fmt.layout.decode n).bind FVal.num

/-- The number of a finite binary32 pattern; `none` for NaN and infinities. -/
def f32Value (bits : Nat) : Option ℚ := FloatFmt.f32.decode bits

/-- A real number is representable in `fmt` when it is the number of a finite pattern (either
zero counts as `0`). -/
def FloatFmt.representable (fmt : FloatFmt) (x : ℝ) : Prop :=
  ∃ n q, fmt.decode n = some q ∧ (q : ℝ) = x


/-! Lemmas: magnitudes increase with the field, `Layout.decode` is injective on patterns of the
layout's width, so `Layout.encode` inverts it, and the finite decoders state today's formulas. -/

theorem Layout.magnitude_zero (eb mb : Nat) : Layout.magnitude eb mb 0 = 0 := by
  simp [Layout.magnitude]

theorem Layout.magnitude_lt_succ (eb mb F : Nat) :
    Layout.magnitude eb mb F < Layout.magnitude eb mb (F + 1) := by
  have hs : 0 < 2 ^ mb := Nat.two_pow_pos _
  have hp : ∀ z : ℤ, (0 : ℚ) < (2 : ℚ) ^ z := fun z => zpow_pos (by norm_num) z
  have hF := Nat.mod_add_div F (2 ^ mb)
  have hr := Nat.mod_lt F hs
  simp only [Layout.magnitude]
  generalize 2 ^ mb = s at hs hF hr ⊢
  have hz : ∀ e : ℤ, e - Layout.bias eb - mb = e - (Layout.bias eb + mb) := fun e => by ring
  simp only [hz]
  generalize Layout.bias eb + (mb : ℤ) = c
  generalize F / s = q at hF ⊢
  generalize F % s = r at hF hr ⊢
  subst hF
  by_cases hc : r + 1 < s
  · have h1 : (r + s * q + 1) / s = q ∧ (r + s * q + 1) % s = r + 1 :=
      (Nat.div_mod_unique hs).mpr ⟨by ring, hc⟩
    rw [h1.1, h1.2]
    split_ifs with hq
    · exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self r) (hp _)
    · exact mul_lt_mul_of_pos_right (by exact_mod_cast (show s + r < s + (r + 1) by omega)) (hp _)
  · have hrs : r + 1 = s := by omega
    have h1 : (r + s * q + 1) / s = q + 1 ∧ (r + s * q + 1) % s = 0 :=
      (Nat.div_mod_unique hs).mpr ⟨by rw [← hrs]; ring, hs⟩
    rw [h1.1, h1.2]
    have h2 : (2 : ℚ) ^ (((q + 1 : ℕ) : ℤ) - c) = 2 * (2 : ℚ) ^ ((q : ℤ) - c) := by
      rw [show ((q + 1 : ℕ) : ℤ) - c = ((q : ℤ) - c) + 1 by push_cast; ring,
        zpow_add_one₀ (by norm_num)]
      ring
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_zero]
    split_ifs with hq
    · subst hq
      simp only [Nat.cast_zero, zero_add] at h2 ⊢
      rw [show ((0 + 1 : ℕ) : ℤ) - c = 1 - c by simp]
      exact mul_lt_mul_of_pos_right (by exact_mod_cast (show r < s by omega)) (hp _)
    · rw [h2]
      have hlt : ((s + r : ℕ) : ℚ) < (s : ℚ) * 2 := by
        have : s + r < s * 2 := by omega
        exact_mod_cast this
      nlinarith [hp ((q : ℤ) - c)]

theorem Layout.magnitude_strictMono (eb mb : Nat) : StrictMono (Layout.magnitude eb mb) :=
  strictMono_nat_of_lt_succ (Layout.magnitude_lt_succ eb mb)

theorem Layout.magnitude_pos {eb mb F : Nat} (h : 0 < F) : 0 < Layout.magnitude eb mb F := by
  rw [← Layout.magnitude_zero eb mb]; exact Layout.magnitude_strictMono eb mb h

theorem Layout.magnitude_nonneg (eb mb F : Nat) : 0 ≤ Layout.magnitude eb mb F := by
  rw [← Layout.magnitude_zero eb mb]; exact (Layout.magnitude_strictMono eb mb).monotone (by omega)

theorem Layout.fieldVal_inj {eb mb F F' : Nat} {neg neg' : Bool}
    (h : Layout.fieldVal eb mb F neg = Layout.fieldVal eb mb F' neg') : F = F' ∧ neg = neg' := by
  unfold Layout.fieldVal at h
  by_cases hF : F = 0 <;> by_cases hF' : F' = 0 <;> simp only [hF, hF', ↓reduceIte] at h
  · exact ⟨by omega, by injection h⟩
  · cases h
  · cases h
  · have p := Layout.magnitude_pos (eb := eb) (mb := mb) (Nat.pos_of_ne_zero hF)
    have p' := Layout.magnitude_pos (eb := eb) (mb := mb) (Nat.pos_of_ne_zero hF')
    have inj := (Layout.magnitude_strictMono eb mb).injective
    injection h with h
    cases neg <;> cases neg' <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_inj] at h
    · exact ⟨inj h, rfl⟩
    · linarith
    · linarith
    · exact ⟨inj h, rfl⟩

/-- The low field and the sign bit of a binary pattern, and the pattern rebuilt from them. -/
theorem Layout.binary_low (eb mb : Nat) (signed : Bool) (sp : Specials) (n : Nat) :
    n % 2 ^ (Layout.binary eb mb signed sp).width % 2 ^ (eb + mb) = n % 2 ^ (eb + mb) :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by simp only [Layout.width]; omega))

theorem Layout.binary_sign (eb mb : Nat) (sp : Specials) (n : Nat) :
    n % 2 ^ (Layout.binary eb mb true sp).width / 2 ^ (eb + mb) % 2 = n / 2 ^ (eb + mb) % 2 := by
  have hs : 0 < 2 ^ (eb + mb) := Nat.two_pow_pos _
  simp only [Layout.width, ↓reduceIte, Nat.mod_pow_succ]
  have hl := Nat.mod_lt n hs
  have hb := Nat.mod_lt (n / 2 ^ (eb + mb)) (show 0 < 2 by omega)
  rw [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hl, Nat.zero_add, Nat.mod_mod]

theorem Layout.binary_pattern (eb mb : Nat) (signed : Bool) (sp : Specials) (n : Nat) :
    n % 2 ^ (Layout.binary eb mb signed sp).width =
      (if (signed && n / 2 ^ (eb + mb) % 2 == 1) then 2 ^ (eb + mb) else 0) +
        n % 2 ^ (eb + mb) := by
  cases signed
  · simp [Layout.width]
  · simp only [Layout.width, ↓reduceIte, Nat.mod_pow_succ, Bool.true_and]
    have hb := Nat.mod_lt (n / 2 ^ (eb + mb)) (show 0 < 2 by omega)
    by_cases h : n / 2 ^ (eb + mb) % 2 = 1
    · simp [h]; ring
    · have h0 : n / 2 ^ (eb + mb) % 2 = 0 := by omega
      simp [h0]

/-- Every datum of a binary pattern is its NaN, the number of its field and sign, or the
infinity of its sign at the infinity field. -/
theorem Layout.decode_binary_cases {eb mb : Nat} {signed : Bool} {sp : Specials} {n : Nat}
    {v : FVal} (h : (Layout.binary eb mb signed sp).decode n = some v) :
    v = .nan (some (n % 2 ^ (Layout.binary eb mb signed sp).width)) ∨
    v = Layout.fieldVal eb mb (n % 2 ^ (eb + mb)) (signed && n / 2 ^ (eb + mb) % 2 == 1) ∨
    (v = .inf (signed && n / 2 ^ (eb + mb) % 2 == 1) ∧
      n % 2 ^ (eb + mb) = (2 ^ eb - 1) * 2 ^ mb) := by
  have hlow := Layout.binary_low eb mb signed sp n
  have hsign : (signed && n % 2 ^ (Layout.binary eb mb signed sp).width / 2 ^ (eb + mb) % 2 == 1)
      = (signed && n / 2 ^ (eb + mb) % 2 == 1) := by
    cases signed
    · rfl
    · rw [Layout.binary_sign]
  have hF := Nat.mod_add_div (n % 2 ^ (eb + mb)) (2 ^ mb)
  simp only [Layout.decode] at h
  rw [hlow, hsign] at h
  generalize (Layout.binary eb mb signed sp).width = w at h ⊢
  cases sp <;> simp only at h <;> (try split_ifs at h) <;> cases h
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | refine Or.inr (Or.inr ⟨rfl, ?_⟩)
  rename_i h1 h2
  rw [h1, h2] at hF
  rw [← hF]
  ring


theorem Layout.fieldVal_ne_nan (eb mb F : Nat) (neg : Bool) (b : Option Nat) :
    Layout.fieldVal eb mb F neg ≠ .nan b := by
  unfold Layout.fieldVal; split_ifs <;> simp

theorem Layout.fieldVal_ne_inf (eb mb F : Nat) (neg neg' : Bool) :
    Layout.fieldVal eb mb F neg ≠ .inf neg' := by
  unfold Layout.fieldVal; split_ifs <;> simp

/-- Two patterns of a binary layout with the same datum agree in the layout's width. -/
theorem Layout.decode_binary_inj {eb mb : Nat} {signed : Bool} {sp : Specials} {m n : Nat}
    {v : FVal} (hm : (Layout.binary eb mb signed sp).decode m = some v)
    (hn : (Layout.binary eb mb signed sp).decode n = some v) :
    m % 2 ^ (Layout.binary eb mb signed sp).width = n % 2 ^ (Layout.binary eb mb signed sp).width
    := by
  rw [Layout.binary_pattern eb mb signed sp m, Layout.binary_pattern eb mb signed sp n]
  rcases Layout.decode_binary_cases hm with h1 | h1 | ⟨h1, f1⟩ <;>
    rcases Layout.decode_binary_cases hn with h2 | h2 | ⟨h2, f2⟩ <;> rw [h1] at h2
  · injection h2 with h2; injection h2 with h2
    rw [← Layout.binary_pattern, ← Layout.binary_pattern]; exact h2
  · exact absurd h2.symm (Layout.fieldVal_ne_nan _ _ _ _ _)
  · cases h2
  · exact absurd h2 (Layout.fieldVal_ne_nan _ _ _ _ _)
  · obtain ⟨hF, hs⟩ := Layout.fieldVal_inj h2
    rw [hF, hs]
  · exact absurd h2 (Layout.fieldVal_ne_inf _ _ _ _ _)
  · cases h2
  · exact absurd h2.symm (Layout.fieldVal_ne_inf _ _ _ _ _)
  · injection h2 with h2
    rw [f1, f2, h2]

/-- Two patterns of a fixed-point layout with the same datum agree in the layout's width. -/
theorem Layout.decode_fixed_inj {w frac m n : Nat} {v : FVal}
    (hm : (Layout.fixed w frac).decode m = some v) (hn : (Layout.fixed w frac).decode n = some v) :
    m % 2 ^ w = n % 2 ^ w := by
  have key : ∀ k : Nat, (Layout.fixed w frac).decode k =
      (let z : ℤ := if k % 2 ^ w < 2 ^ (w - 1) then ((k % 2 ^ w : ℕ) : ℤ)
        else ((k % 2 ^ w : ℕ) : ℤ) - 2 ^ w
        if z = 0 then some (.zero false) else some (.fin ((z : ℚ) * (2 : ℚ) ^ (-(frac : ℤ))))) :=
    fun _ => rfl
  rw [key] at hm hn
  have hp : (2 : ℚ) ^ (-(frac : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hzeq : ∀ k : Nat, (if k % 2 ^ w < 2 ^ (w - 1) then ((k % 2 ^ w : ℕ) : ℤ)
      else ((k % 2 ^ w : ℕ) : ℤ) - 2 ^ w) = (if m % 2 ^ w < 2 ^ (w - 1) then
        ((m % 2 ^ w : ℕ) : ℤ) else ((m % 2 ^ w : ℕ) : ℤ) - 2 ^ w) →
      k = n → k % 2 ^ w = m % 2 ^ w := by
    intro k hk _
    have hw : w = 0 ∨ 2 ^ w = 2 * 2 ^ (w - 1) := by
      rcases Nat.eq_zero_or_pos w with h | h
      · exact Or.inl h
      · right; rw [← Nat.pow_succ']; congr 1; omega
    have hkl := Nat.mod_lt k (Nat.two_pow_pos w)
    have hml := Nat.mod_lt m (Nat.two_pow_pos w)
    have hz : ((2 ^ w : ℕ) : ℤ) = 2 ^ w := by push_cast; rfl
    rcases hw with hw | hw
    · subst hw; simp only [pow_zero, Nat.mod_one]
    · have hw' : ((2 : ℤ) ^ w) = 2 * 2 ^ (w - 1) := by exact_mod_cast hw
      have hc : ((2 : ℤ) ^ (w - 1)) = ((2 ^ (w - 1) : ℕ) : ℤ) := by push_cast; rfl
      rw [hw'] at hk
      split_ifs at hk <;> omega
  symm
  apply hzeq n _ rfl
  generalize hzm : (if m % 2 ^ w < 2 ^ (w - 1) then ((m % 2 ^ w : ℕ) : ℤ)
    else ((m % 2 ^ w : ℕ) : ℤ) - 2 ^ w) = zm at hm
  generalize hzn : (if n % 2 ^ w < 2 ^ (w - 1) then ((n % 2 ^ w : ℕ) : ℤ)
    else ((n % 2 ^ w : ℕ) : ℤ) - 2 ^ w) = zn at hn
  simp only at hm hn
  by_cases h1 : zm = 0 <;> by_cases h2 : zn = 0 <;> simp only [h1, h2, ↓reduceIte] at hm hn
  · rw [h1, h2]
  · rw [← hm] at hn; cases hn
  · rw [← hm] at hn; cases hn
  · rw [← hm] at hn
    injection hn with hn
    injection hn with hn
    have := mul_right_cancel₀ hp hn
    exact_mod_cast this

/-- Two patterns of the layout's width with the same datum are equal. -/
theorem Layout.decode_inj {L : Layout} {m n : Nat} {v : FVal} (hm : m < 2 ^ L.width)
    (hn : n < 2 ^ L.width) (h1 : L.decode m = some v) (h2 : L.decode n = some v) : m = n := by
  cases L with
  | binary eb mb signed sp =>
    have := Layout.decode_binary_inj h1 h2
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this
  | fixed w frac =>
    have := Layout.decode_fixed_inj h1 h2
    simp only [Layout.width] at hm hn
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at this

/-- `Layout.encode` inverts `Layout.decode` on the patterns of the layout's width. -/
theorem Layout.encode_decode {L : Layout} {n : Nat} {v : FVal} (hn : n < 2 ^ L.width)
    (h : L.decode n = some v) : L.encode v = some n := by
  unfold Layout.encode
  rw [List.find?_range_eq_some]
  refine ⟨by simp [h], List.mem_range.mpr hn, fun j hj => ?_⟩
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  intro hj'
  have := Layout.decode_inj (by omega) hn hj' h
  omega

/-- A pattern `Layout.encode` gives has the layout's width and decodes to the datum. -/
theorem Layout.decode_of_encode {L : Layout} {n : Nat} {v : FVal} (h : L.encode v = some n) :
    n < 2 ^ L.width ∧ L.decode n = some v := by
  unfold Layout.encode at h
  rw [List.find?_range_eq_some] at h
  obtain ⟨h1, h2, -⟩ := h
  exact ⟨List.mem_range.mp h2, by simpa using h1⟩


theorem FVal.num_fieldVal (eb mb F : Nat) (neg : Bool) :
    (Layout.fieldVal eb mb F neg).num =
      some (if neg then -Layout.magnitude eb mb F else Layout.magnitude eb mb F) := by
  unfold Layout.fieldVal
  split_ifs with h <;> simp [FVal.num, h, Layout.magnitude_zero]

/-- The layout of a payload format is a signed binary layout with the format's field widths;
only `.e4m3` has the `.e4m3` specials. -/
theorem FloatFmt.layout_eq (fmt : FloatFmt) : fmt.layout =
    .binary fmt.expBits fmt.mantBits true (if fmt = .e4m3 then .e4m3 else .ieee) := by
  cases fmt <;> rfl

/-- Today's magnitude formula, with the bias as a natural number. -/
theorem FloatFmt.magnitude_eq (fmt : FloatFmt) (F : Nat) : fmt.magnitude F =
    let e := F / 2 ^ fmt.mantBits
    let m := F % 2 ^ fmt.mantBits
    if e = 0 then (m : ℚ) * (2 : ℚ) ^ ((1 : ℤ) - fmt.bias - fmt.mantBits)
    else ((2 ^ fmt.mantBits + m : ℕ) : ℚ) * (2 : ℚ) ^ ((e : ℤ) - fmt.bias - fmt.mantBits) := by
  have hb : Layout.bias fmt.expBits = (fmt.bias : ℤ) := by
    simp only [Layout.bias, FloatFmt.bias]
    have := Nat.one_le_two_pow (n := fmt.expBits - 1)
    push_cast [Nat.cast_sub this]; rfl
  simp only [FloatFmt.magnitude, Layout.magnitude, hb]

/-- Today's finite decoder: the field and sign of the pattern, `none` at the infinity and NaN
encodings. -/
theorem FloatFmt.decode_eq (fmt : FloatFmt) (n : Nat) : fmt.decode n =
    let F := n % 2 ^ (fmt.expBits + fmt.mantBits)
    if F / 2 ^ fmt.mantBits = 2 ^ fmt.expBits - 1 ∧
        (fmt ≠ .e4m3 ∨ F % 2 ^ fmt.mantBits = 2 ^ fmt.mantBits - 1) then none
    else some (if n / 2 ^ (fmt.expBits + fmt.mantBits) % 2 = 0 then fmt.magnitude F
      else -fmt.magnitude F) := by
  have hL := FloatFmt.layout_eq fmt
  have hs := Layout.binary_sign fmt.expBits fmt.mantBits
    (if fmt = .e4m3 then .e4m3 else .ieee) n
  have hl := Layout.binary_low fmt.expBits fmt.mantBits true
    (if fmt = .e4m3 then .e4m3 else .ieee) n
  have hb := Nat.mod_lt (n / 2 ^ (fmt.expBits + fmt.mantBits)) (show 0 < 2 by omega)
  unfold FloatFmt.decode
  rw [hL]
  simp only [Layout.decode, hl, hs, Bool.true_and]
  simp only [FloatFmt.magnitude]
  generalize n % 2 ^ (fmt.expBits + fmt.mantBits) = F
  generalize n / 2 ^ (fmt.expBits + fmt.mantBits) % 2 = b at hb ⊢
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> by_cases he : fmt = .e4m3 <;>
    simp only [he, ↓reduceIte, ne_eq, not_true_eq_false, false_or, not_false_eq_true, true_or,
      and_true] <;>
    split_ifs <;> simp_all [FVal.num_fieldVal] <;> rfl


/-- The pattern of field `F` and sign `neg` of a binary layout: its low bits are `F` and its sign
bit is `neg`. -/
theorem Layout.binary_pattern_parts {eb mb : Nat} {signed : Bool} {sp : Specials} {F : Nat}
    {neg : Bool} (hF : F < 2 ^ (eb + mb)) (hs : signed = false → neg = false) :
    ((if neg then 2 ^ (eb + mb) else 0) + F) % 2 ^ (Layout.binary eb mb signed sp).width =
      (if neg then 2 ^ (eb + mb) else 0) + F ∧
    ((if neg then 2 ^ (eb + mb) else 0) + F) % 2 ^ (eb + mb) = F ∧
    (signed && ((if neg then 2 ^ (eb + mb) else 0) + F) / 2 ^ (eb + mb) % 2 == 1) = neg := by
  have hk : 0 < 2 ^ (eb + mb) := Nat.two_pow_pos _
  cases signed
  · have := hs rfl; subst this
    simp only [Layout.width, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero,
      Nat.mod_eq_of_lt hF, Bool.false_and, and_self]
  · have h2 : 2 ^ (Layout.binary eb mb true sp).width = 2 * 2 ^ (eb + mb) := by
      simp only [Layout.width, ↓reduceIte, Nat.pow_succ]; ring
    rw [h2]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.div_eq_of_lt hF,
        Nat.zero_mod, Bool.true_and, Nat.mod_eq_of_lt hF]
      exact ⟨Nat.mod_eq_of_lt (by omega), by simp⟩
    · simp only [↓reduceIte, Bool.true_and]
      refine ⟨Nat.mod_eq_of_lt (by omega), by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hF], ?_⟩
      rw [Nat.add_div_left _ hk, Nat.div_eq_of_lt hF]; rfl

/-- A field below the infinity field of an IEEE layout decodes to its number. -/
theorem Layout.decode_field_ieee {eb mb : Nat} {signed : Bool} {F : Nat} {neg : Bool}
    (hF : F < (2 ^ eb - 1) * 2 ^ mb) (hs : signed = false → neg = false) :
    (Layout.binary eb mb signed .ieee).decode ((if neg then 2 ^ (eb + mb) else 0) + F) =
      some (Layout.fieldVal eb mb F neg) := by
  have hk : F < 2 ^ (eb + mb) := by
    have : (2 ^ eb - 1) * 2 ^ mb ≤ 2 ^ (eb + mb) := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    omega
  obtain ⟨h1, h2, h3⟩ := Layout.binary_pattern_parts (signed := signed) (sp := .ieee) hk hs
  have he : ¬ F / 2 ^ mb = 2 ^ eb - 1 := by
    have := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos mb)).mpr hF
    omega
  simp only [Layout.decode, h1, h2, h3, he, ↓reduceIte]

/-- A field below the NaN field of an `.e4m3` layout decodes to its number. -/
theorem Layout.decode_field_e4m3 {eb mb : Nat} {signed : Bool} {F : Nat} {neg : Bool}
    (hF : F < 2 ^ (eb + mb) - 1) (hs : signed = false → neg = false) :
    (Layout.binary eb mb signed .e4m3).decode ((if neg then 2 ^ (eb + mb) else 0) + F) =
      some (Layout.fieldVal eb mb F neg) := by
  obtain ⟨h1, h2, h3⟩ := Layout.binary_pattern_parts (signed := signed) (sp := .e4m3)
    (show F < 2 ^ (eb + mb) by omega) hs
  have he : ¬ (F / 2 ^ mb = 2 ^ eb - 1 ∧ F % 2 ^ mb = 2 ^ mb - 1) := by
    rintro ⟨ha, hb⟩
    have hd := Nat.mod_add_div F (2 ^ mb)
    rw [ha, hb] at hd
    have hp : 2 ^ (eb + mb) = 2 ^ mb * 2 ^ eb := by rw [Nat.pow_add, Nat.mul_comm]
    have h1 := Nat.one_le_two_pow (n := mb)
    have h2 := Nat.one_le_two_pow (n := eb)
    rw [hp] at hF
    have : 2 ^ mb - 1 + 2 ^ mb * (2 ^ eb - 1) = 2 ^ mb * 2 ^ eb - 1 := by
      rw [Nat.mul_sub, Nat.mul_one]
      have : 2 ^ mb ≤ 2 ^ mb * 2 ^ eb := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega
  simp only [Layout.decode, h1, h2, h3, he, ↓reduceIte]

/-- The infinity pattern of an IEEE layout decodes to the infinity of its sign. -/
theorem Layout.decode_infPattern_ieee {eb mb : Nat} {signed : Bool} {neg : Bool}
    (hs : signed = false → neg = false) :
    (Layout.binary eb mb signed .ieee).decode
      ((Layout.binary eb mb signed .ieee).infPattern neg) = some (.inf neg) := by
  have hk : (2 ^ eb - 1) * 2 ^ mb < 2 ^ (eb + mb) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) (by omega))
      (Nat.two_pow_pos _)
  obtain ⟨h1, h2, h3⟩ := Layout.binary_pattern_parts (signed := signed) (sp := .ieee) hk hs
  have hm := Nat.two_pow_pos mb
  simp only [Layout.infPattern, Layout.decode, h1, h2, h3, Nat.mul_div_cancel _ hm,
    Nat.mul_mod_left, ↓reduceIte]

/-- A field up to `topField` of a payload format decodes to its number. -/
theorem FloatFmt.decode_field (fmt : FloatFmt) {F : Nat} (neg : Bool)
    (hF : F ≤ fmt.layout.topField) :
    fmt.layout.decode ((if neg then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F) =
      some (Layout.fieldVal fmt.expBits fmt.mantBits F neg) := by
  have hL := FloatFmt.layout_eq fmt
  have hpos : 0 < (2 ^ fmt.expBits - 1) * 2 ^ fmt.mantBits := by cases fmt <;> decide
  rw [hL] at hF ⊢
  by_cases he : fmt = .e4m3
  · simp only [he, ↓reduceIte, Layout.topField] at hF ⊢
    have h2 : 2 ≤ 2 ^ (FloatFmt.e4m3.expBits + FloatFmt.e4m3.mantBits) := by decide
    exact Layout.decode_field_e4m3 (by omega) (by simp)
  · simp only [he, ↓reduceIte, Layout.topField] at hF ⊢
    exact Layout.decode_field_ieee (by omega) (by simp)

/-- `-0` of a payload format: the sign pattern decodes to the negative zero. -/
theorem FloatFmt.decode_signPattern (fmt : FloatFmt) :
    fmt.layout.decode fmt.layout.signPattern = some (.zero true) := by
  have h := FloatFmt.decode_field fmt (F := 0) true (by cases fmt <;> decide)
  have hw : fmt.layout.signPattern = 2 ^ (fmt.expBits + fmt.mantBits) := by
    cases fmt <;> rfl
  rw [hw]
  simpa [Layout.fieldVal] using h

/-- The infinity pattern of a payload format with infinities decodes to the infinity of its
sign. -/
theorem FloatFmt.decode_infPattern (fmt : FloatFmt) (h : fmt ≠ .e4m3) (neg : Bool) :
    fmt.layout.decode (fmt.layout.infPattern neg) = some (.inf neg) := by
  rw [FloatFmt.layout_eq fmt]
  simp only [h, ↓reduceIte]
  exact Layout.decode_infPattern_ieee (by simp)

end PTX
