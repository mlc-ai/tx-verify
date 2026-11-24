-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule
public import Core.Isa.Mem

@[expose] public section

/-!
# Conversions

`cvt` between integer and floating types, and `cvt.pack`.
-/

namespace PTX

/-! ## PROG-ISA-CVT — conversions
Statement: A conversion is its destination and source types, its rounding modifier, its `.ftz`,
  `.sat`, `.relu`, `.satfinite` and `.pzo` qualifiers, whether it is scaled or a `cvt.pack`, its
  destination register with the extension that fills a wider one, and its sources. Every entry of
  the `cvt` family decodes to it, and an operand of `cvt d, a` may be a register wider than its
  type, except for a `.bf16` operand.

Defs: CvtRnd, CvtRnd.isInt, CvtInstr, Decode.CvtInstr.rnd?, Decode.CvtInstr.intSrc,
  Decode.CvtInstr.intDst, Decode.CvtInstr.floatSrcOf, Decode.CvtInstr.floatDstOf,
  Decode.CvtInstr.srcOf, Decode.CvtInstr.ofRaw, CvtInstr.plain, CvtInstr.widens,
  CvtInstr.narrows, CvtInstr.exact, CvtInstr.rule, CvtInstr.widenF16?, CvtInstr.packF16?

Source:
- §9.7.10.24: "cvt{.irnd}{.ftz}{.sat}.dtype.atype d, a;"
- §9.7.10.24: "cvt.frnd2{.relu}{.satfinite}{.pzo}.f16x2.f32 d, a, b;"
- §9.7.10.24: "A source register wider than the specified type may be used, except when the source
    operand has .bf16 or .bf16x2 format."
- §9.7.10.24: "The lower n bits corresponding to the instruction-type width are used in the
    conversion."
- §9.7.10.24: "A destination register wider than the specified type may be used, except when the
    destination operand has .bf16 , .bf16x2 or .tf32 format."
- §9.7.10.24: "The result of conversion is sign-extended to the destination register width for
    signed integers, and is zero-extended to the destination register width for unsigned, bit-size,
    and floating-point types."
- §9.7.10.25: "cvt.pack.sat.convertType.abType d, a, b;"
- §9.7.10.24: "cvt.rs{.relu}{.satfinite}.f16x2.f32 d, a, b, rbits;"
- §9.7.10.24: "cvt.rs{.relu}.satfinite.f8x4type.f32 d, {a, b, e, f}, rbits;"
- §9.7.10.24: "cvt.frnd2.satfinite{.relu}{.pzo}{.scaled::n1::ue8m0}.f8x2type.f32 d, a, b{,
    scale-factor};"
- §9.7.10.24: "cvt.rn{.relu}{.satfinite}{.scaled::n2::ue8m0}.bf16x2.f8x2type d, a{, scale-factor};"
- §9.7.10.24: "When converting from .bf16x2 , each input packed in operand a is converted to .s2f6
    value"
- §9.7.10.24: "d[15:8] = convert(a[15:8] / scale-factor[15:8]); d[7:0] = convert(a[7:0] /
    scale-factor[7:0]);"
- §5.2.3: "The internal layout of tf32 format is implementation defined."
- §9.4.1 (Table 27): "Integer source registers may be used with any appropriately-sized bit-size or
    integer instruction type."
- §9.4.1 (Table 27): "Bit-size source registers may be used with any appropriately-sized instruction
    type. The data are truncated (“chopped”) to the instruction-type size and interpreted according
    to the instruction type."
- §9.4.1 (Table 28): "Destination register size must be of equal or greater size than the
    instruction-type size."
- §9.4.1 (Table 28): "Bit-size destination registers may be used with any appropriately-sized
    instruction type."

Direction: stricter

Applies: Every instruction of the `cvt` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types, or wider for an operand of `cvt d, a` whose type is not
  `.bf16`.

Effect: Representation; `CvtInstr.rule` selects THREAD-CVT for the conversions that `CvtInstr.exact`
  lists and no rule otherwise. An integer source of `cvt d, a` may be a register or special register
  wider than the source type (`Decode.CvtInstr.intSrc`), whose low bits the conversion reads. An
  integer destination may be a register wider than the destination type, of at most 64 bits
  (`Decode.CvtInstr.intDst`); the conversion then records the extension `MemExt.sign` for a signed
  type and `MemExt.zero` otherwise, the representation `ld` uses for the same rule (PROG-ISA-MEM).
  A floating source of type `.f16`, `.f32` or `.f64` may be a wider register
  (`Decode.CvtInstr.floatSrcOf`), whose low bits the conversion reads, and a floating destination of
  these types may be a register wider than the type, of at most 64 bits, which the result fills
  zero-extended (`MemExt.zero`, `Decode.CvtInstr.floatDstOf`). A `.bf16` operand and every operand
  of the packed forms keep the exact width of their type. A register declaration records only a
  width, so the decoding accepts a wider register of any type; Table 27 and Table 28 accept only a
  bit-size register wider than a floating instruction type. A destination register wider than 64
  bits is rejected (stricter: the tables also allow a `.b128` register). `CvtInstr.exact` lists the
  conversions THREAD-CVT gives a rule: every integer-to-integer conversion and `cvt.pack`; a
  floating-to-integer conversion with an integer rounding modifier; between `.f16`, `.bf16`, `.f32`
  and `.f64`, a widening without a rounding modifier (`CvtInstr.widens`), a rounding to an
  integral value at the same format, and a narrowing with `.rn`, `.rz`, `.rm` or `.rp`
  (`CvtInstr.narrows`); an integer-to-floating conversion with one of these four; two `.f32`
  sources to `.f16x2` or `.bf16x2` with one of these four or with `.rs`, and to `.e4m3x2`,
  `.e5m2x2`, `.e2m1x2`, `.e2m3x2`, `.e3m2x2`, `.ue8m0x2`, `.ue5m3x2` or `.s2f6x2` with an optional
  scale factor; an `.f16x2` or `.bf16x2` source to these types except `.s2f6x2`; and the widening
  of these types to `.f16x2` and `.bf16x2`, with a scale factor only to `.bf16x2`. The grammar
  requires a rounding modifier for a conversion that narrows and rejects a floating rounding
  modifier on one that widens. The others have no rule: a conversion to `.tf32`, whose internal
  layout is implementation defined; `.s2f6x2` from `.bf16x2`, whose Description converts the two
  `.bf16` inputs of `a` while its Semantics converts `a[15:8]` and `a[7:0]`; and `.rs` to the
  four-element types, whose random bit layouts the manual gives only as figures.
  `cvt.f32.f16` without qualifiers and `cvt.rn.f16x2.f32` have rules like the other conversions;
  ASM-IDEAL selects them by `CvtInstr.widenF16?` and `CvtInstr.packF16?`.
-/

/-- The rounding modifier of a conversion. -/
inductive CvtRnd where
  | rn | rz | rm | rp | rni | rzi | rmi | rpi | rna | rs
  deriving DecidableEq, Repr

/-- Whether a rounding modifier is an integer rounding modifier (`.rni`, `.rzi`, `.rmi`, `.rpi`). -/
def CvtRnd.isInt : CvtRnd → Bool
  | .rni | .rzi | .rmi | .rpi => true
  | _ => false

/-- A conversion: destination and source types, rounding, qualifiers, the destination register,
how the result fills a destination register wider than its type, and the sources in operand
order. -/
structure CvtInstr where
  dst : DType
  src : DType
  rnd : Option CvtRnd := none
  ftz : Bool := false
  sat : Bool := false
  relu : Bool := false
  satfinite : Bool := false
  pzo : Bool := false
  scaled : Bool := false
  pack : Bool := false
  d : Nat
  ext : MemExt := .same
  srcs : List Opnd
  deriving DecidableEq, Repr

namespace Decode
open PTX.Syntax

/-- The rounding modifier of a conversion. -/
def CvtInstr.rnd? : Option Isa.Token → M (Option CvtRnd)
  | none => pure none
  | some .rn => pure (some .rn) | some .rz => pure (some .rz) | some .rm => pure (some .rm)
  | some .rp => pure (some .rp) | some .rni => pure (some .rni) | some .rzi => pure (some .rzi)
  | some .rmi => pure (some .rmi) | some .rpi => pure (some .rpi) | some .rna => pure (some .rna)
  | some .rs => pure (some .rs)
  | some _ => throw "conversion rounding modifier"

/-- An integer source of `w` bits: a register or special register of at least `w` bits (Table 27),
or any other source of `w` bits. -/
def CvtInstr.intSrc (env : Env) (w : Nat) : Operand → M Opnd
  | .register r => match SReg.ofName? r with
    | some s => do
      env.sregAllowed r s
      if w ≤ s.width then pure (.sreg s) else throw s!"{r} is {s.width}-bit"
    | none => do
      let (rw, i) ← regInfo env.classes r
      unless w ≤ rw do throw s!"register {r} has width {rw}, expected at least {w}"
      pure (.reg i)
  | o => src env w o

/-- The destination of an integer type of kind `k` and `w` bits: a register of `w` to 64 bits, and
the extension that fills it (Table 28: sign-extended for a signed type, zero-extended otherwise). -/
def CvtInstr.intDst (env : Env) (k : IType) (w : Nat) : Operand → M (Nat × MemExt)
  | .register r => do
    let (rw, i) ← regInfo env.classes r
    unless w ≤ rw ∧ rw ≤ 64 do throw s!"register {r} has width {rw}, expected {w} to 64"
    let ext := if rw = w then MemExt.same else if k = .s then .sign rw else .zero rw
    pure (i, ext)
  | o => throw s!"expected register, got {repr o}"

/-- A floating source of type `f` of `cvt d, a`: a register of at least the type's width
(Table 27, §9.7.10.24 Notes), whose low bits the conversion reads, except for `.bf16`, whose
register has its exact width; any other operand as a floating source of the type's width. -/
def CvtInstr.floatSrcOf (env : Env) (f : FType) : Operand → M Opnd
  | .register r =>
    let w := (DType.float f).width
    if f ≠ .bf16 ∧ (SReg.ofName? r).isNone then do
      let (rw, i) ← regInfo env.classes r
      unless w ≤ rw do throw s!"register {r} has width {rw}, expected at least {w}"
      pure (.reg i)
    else floatSrc env w (.register r)
  | o => floatSrc env (DType.float f).width o

/-- The destination of a floating type `f` of `cvt d, a`: a register of the type's width to 64 bits
(Table 28, §9.7.10.24 Notes), zero-extended when wider, except for `.bf16`, whose register has its
exact width. -/
def CvtInstr.floatDstOf (env : Env) (f : FType) : Operand → M (Nat × MemExt)
  | .register r => do
    let w := (DType.float f).width
    let (rw, i) ← regInfo env.classes r
    unless w ≤ rw ∧ rw ≤ 64 ∧ (f ≠ .bf16 ∨ rw = w) do
      throw s!"register {r} has width {rw}, expected {w}{if f = .bf16 then "" else " to 64"}"
    pure (i, if rw = w then MemExt.same else .zero rw)
  | o => throw s!"expected register, got {repr o}"

/-- The source of `cvt d, a` of type `t`: an integer source (`CvtInstr.intSrc`) or a floating
one (`CvtInstr.floatSrcOf`). -/
def CvtInstr.srcOf (env : Env) : DType → Operand → M Opnd
  | .int _ sw => CvtInstr.intSrc env sw
  | .float f => CvtInstr.floatSrcOf env f
  | _ => fun _ => throw "conversion source type"

/-- The `cvt`-family instruction of a recognized instruction. -/
def CvtInstr.ofRaw (env : Env) (r : Isa.Raw) : M CvtInstr := do
  let pack := match r.entry with | .cvt_pack | .cvt_pack_c => true | _ => false
  let dst ← dtype (if pack then r.get .convert else r.get .dtype)
  let src ← dtype (if pack then r.get .abtype else r.get .atype)
  let (d, ext, srcs) ← match r.entry, dst, src with
    | .cvt, .int k w, _ => do
      let (d, ext) ← CvtInstr.intDst env k w (← arg r "d")
      pure (d, ext, [← CvtInstr.srcOf env src (← arg r "a")])
    | .cvt, .float f, _ => do
      let (d, ext) ← CvtInstr.floatDstOf env f (← arg r "d")
      pure (d, ext, [← CvtInstr.srcOf env src (← arg r "a")])
    | _, _, _ => do
      let (dsts, srcs) ← operands env r
      let [some d] := dsts | throw "conversion destination"
      pure (d, MemExt.same, srcs)
  return { dst, src, rnd := ← CvtInstr.rnd? (r.get .rnd), ftz := flag r .ftz, sat := flag r .sat,
           relu := flag r .relu, satfinite := flag r .satfinite, pzo := flag r .pzo,
           scaled := flag r .scaled, pack, d, ext, srcs }

end Decode

/-- A conversion without qualifiers other than the rounding modifier. -/
def CvtInstr.plain (c : CvtInstr) : Bool :=
  !c.ftz && !c.sat && !c.relu && !c.satfinite && !c.pzo && !c.scaled && !c.pack

/-- `cvt.f32.f16 d, a` without qualifiers: its destination and source. -/
def CvtInstr.widenF16? (c : CvtInstr) : Option (Nat × Opnd) :=
  match c.dst, c.src, c.rnd, c.srcs with
  | .float .f32, .float .f16, none, [a] => if c.plain then some (c.d, a) else none
  | _, _, _, _ => none

/-- `cvt.rn.f16x2.f32 d, a, b` without other qualifiers: its destination and sources. -/
def CvtInstr.packF16? (c : CvtInstr) : Option (Nat × Opnd × Opnd) :=
  match c.dst, c.src, c.rnd, c.srcs with
  | .packed (.float .f16) 2, .float .f32, some .rn, [a, b] =>
    if c.plain then some (c.d, a, b) else none
  | _, _, _, _ => none

/-- Whether `cvt` from `sf` to `df`, both among `.f16`, `.bf16`, `.f32` and `.f64`, widens: the
same format, `.f16` or `.bf16` to `.f32` or `.f64`, or `.f32` to `.f64`. -/
def CvtInstr.widens (df sf : FType) : Bool :=
  df == sf || (sf == .f16 || sf == .bf16) && (df == .f32 || df == .f64) || sf == .f32 && df == .f64

/-- Whether `cvt` from `sf` to `df`, both among `.f16`, `.bf16`, `.f32` and `.f64`, narrows: a
smaller destination, or between `.f16` and `.bf16`. -/
def CvtInstr.narrows (df sf : FType) : Bool :=
  sf == .f64 && df != .f64 || sf == .f32 && (df == .f16 || df == .bf16) ||
    sf == .f16 && df == .bf16 || sf == .bf16 && df == .f16

/-- Whether THREAD-CVT gives the conversion a rule (PROG-ISA-CVT): an integer conversion or
`cvt.pack`; a floating-to-integer conversion with an integer rounding modifier; between `.f16`,
`.bf16`, `.f32` and `.f64`, a widening without a rounding modifier, an integer rounding modifier at
the same format, or a narrowing with `.rn`, `.rz`, `.rm` or `.rp`; an integer-to-floating
conversion with one of these; two `.f32` sources to `.f16x2` or `.bf16x2` with one of these or with
`.rs`, or to a packed 4-, 6- or 8-bit type with one of these and an optional scale factor; an
`.f16x2` or `.bf16x2` source to such a packed type except `.s2f6x2`; and the widening of a packed
4-, 6- or 8-bit type to `.f16x2` or `.bf16x2`, scaled only to `.bf16x2`. A floating destination of
`cvt d, a` may be zero-extended into a wider register. -/
def CvtInstr.exact (c : CvtInstr) : Bool :=
  let one := c.srcs.length == 1
  let n := c.srcs.length
  let irnd := match c.rnd with | some r => r.isInt | none => false
  let frnd := match c.rnd with | some .rn | some .rz | some .rm | some .rp => true | _ => false
  let fext := match c.ext with | .sign _ => false | _ => true
  let q := !c.relu && !c.satfinite && !c.pzo && !c.scaled
  let pay (f : FType) : Bool := [FType.f16, .bf16, .f32, .f64].contains f
  let half (f : FType) : Bool := f == .f16 || f == .bf16
  let small (f : FType) : Bool :=
    [FType.e4m3, .e5m2, .ue8m0, .e2m1, .e2m3, .e3m2, .ue5m3, .s2f6].contains f
  let packedQ := !c.pack && !c.ftz && !c.sat && c.ext == .same
  match c.dst, c.src with
  | .int _ _, .int _ _ =>
    q && !c.ftz && (if c.pack then c.sat && c.ext == .same else c.rnd.isNone && one)
  | .int _ _, .float f => q && !c.pack && one && irnd && pay f
  | .float df, .float sf =>
    !c.scaled && !c.pack && one && fext && pay df && pay sf &&
      (match c.rnd with
        | none => q && CvtInstr.widens df sf
        | some r => if r.isInt then q && df == sf else frnd && CvtInstr.narrows df sf)
  | .float df, .int _ _ => q && !c.pack && one && fext && frnd && pay df
  | .packed (.float df) 2, .float .f32 =>
    packedQ &&
      (if c.rnd == some .rs then half df && !c.scaled && !c.pzo && n == 3
      else frnd && (half df && !c.scaled && n == 2 || small df && (n == 2 || c.scaled && n == 3)))
  | .packed (.float df) 2, .packed (.float sf) 2 =>
    packedQ && frnd &&
      (if half sf then small df && df != .s2f6 && (one || c.scaled && n == 2)
      else half df && small sf && !c.pzo && (one || c.scaled && df == .bf16 && n == 2))
  | _, _ => false

/-- The rule of a conversion: THREAD-CVT for the conversions the model gives exactly
(`CvtInstr.exact`), none otherwise. -/
def CvtInstr.rule (c : CvtInstr) : Option RuleId :=
  if c.exact then some .threadCvt else none

end PTX
