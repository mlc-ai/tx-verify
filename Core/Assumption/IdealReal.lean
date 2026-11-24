-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Access
public import Core.Tc.TcMmaValue
public import Mathlib.Data.EReal.Operations

@[expose] public section

/-!
# Assumption constructor `idealReal`

A kernel declares an ideal-real assumption with `Assumption.idealReal`, naming exactly the
floating instruction forms, MMA kinds and atomic or reduction elements its proof reads as exact real
arithmetic. This file is not itself an assumption.
-/

namespace PTX.Assumption
noncomputable section

/-! ## ASM-IDEAL — ideal-real floating arithmetic, for the forms a kernel names
Statement: For the floating instruction forms, MMA kinds and atomic and reduction elements a kernel
  names, the model computes each result as the exact real number of the operation, without rounding,
  overflow or subnormal values, and in place of the Core rule. An infinite operand of a floating
  instruction form is read as that infinity, and the Core rule applies to a NaN operand, `∞ - ∞` and
  `0 · ∞`.

Defs: Assumption.floatFmtText, Assumption.FloatForm, Assumption.isInfConst,
  Assumption.FloatForm.ofOp, Assumption.FloatForm.text, Assumption.f8f6f4Text,
  Assumption.mmaKindText, Assumption.rmwText, Assumption.IdealScope, Assumption.IdealScope.text,
  Assumption.readEReal, Assumption.readEReal.ofDatum, Assumption.readERealOpnd,
  Assumption.readERealPair, Assumption.addEReal, Assumption.mulEReal, Assumption.erealValue,
  Assumption.erealCompare, Assumption.bindRead, Assumption.execIdealFloat, Assumption.idealRmw,
  Assumption.idealMmaElement, Assumption.idealMmaDot, Assumption.idealMmaAccumulator,
  Assumption.tf32Value, Assumption.execIdealMma, Assumption.dtypeText, Assumption.warpMmaText,
  Assumption.idealWarpElem, Assumption.idealWarpMma, Assumption.idealReal

Source:
- Explicit numerical interpretation
- §9.7.3, §9.7.10.24 (the hardware operations this reading idealizes)
- §9.7.3.3
- §9.7.3.4
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] + fB[i];"
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] - fB[i];"
- §9.7.3.6 (`.f32x2`): "d[i] = fA[i] * fB[i] + fC[i];"
- §9.7.3.6 (rounding modifiers): ".rn mantissa LSB rounds to nearest even"
- §9.7.3.6 (rounding modifiers): ".rm mantissa LSB rounds toward negative infinity"
- §9.7.3.11
- §9.7.3.12: "Store the maximum of a , b and optionally c in d ."
- §9.7.7.2
- §9.3.1.2: "If both operands are numeric values (not NaN ), then these comparisons have the same
    result as their ordered counterparts."
- §4.5.2 (`0f` constants are IEEE 754 single-precision bit patterns)

Direction: not-conservative

Effect: `idealReal name scope why` replaces, for exactly the forms in `scope`, floating arithmetic
  and conversion (`float`, one `FloatForm` per instruction form, `FloatForm.ofOp`), floating MMA
  (`mma`, by `kind`) and the floating elements of `atom`, `red` and tensor reductions (`rmw`, by
  operation and element type, THREAD-ATOMIC-OP) with exact real operations. A kernel assumption's
  local rule is consulted before the Core rule and replaces it for the instructions it selects
  (THREAD-LOCAL), so a selected form has the ideal result although Core has a rule for it. `add`,
  `mul` and `fma` are exact for every rounding modifier. A floating instruction form reads each
  operand in the extended reals (`readEReal`): a payload of the format is its number, every other
  value the datum THREAD-NUM's `classify` reads, with either zero `0` and an infinity `⊥` or `⊤`
  (`0fFF800000` and `0f7F800000` included). The operation is the extended-real one: `min`/`max` of
  two or three values are the minimum and maximum, and `setp` is the comparison (`erealCompare`),
  where an unordered comparison equals its ordered counterpart since no operand is NaN (§9.3.1.2).
  The rule declines, and the Core rule (THREAD-FLOAT, THREAD-CVT) gives the result, when an operand
  is NaN or the operation is `∞ - ∞` (`addEReal`) or `0 · ∞` (`mulEReal`), which have no
  extended-real value. A real result is the payload `.float fmt x` and an infinite result the bits
  of that infinity (`erealValue`). The reading has one zero: a `-0` operand reads as `0` and a zero
  result is the payload `+0`, where the Core rule may give `-0` (`x - x` under `.rm`, `cvt.f32.f16`
  of `-0`). `setpInf` is the form of a `setp` with an infinite constant operand; it computes as
  `setp`, and a scope that names `setp` but not `setpInf` leaves such an instruction to the Core
  rule. The assumption changes the values the selected instructions produce. When an integer or
  bit instruction reads such a result it reads the bits of its encoding (`FloatFmt.encode`,
  THREAD-BITS), so control flow, addresses and loop bounds that depend on floating-point bits are
  determined by the ideal values, and all four conclusions (safe, progress, terminates, result)
  hold for the ideal machine. A `.f32x2` operand is split into its two 32-bit halves, §9.7.3:
  "fA[0] = a[0:31]; fA[1] = a[32:63];" (`readERealPair`). Results are payloads `.float fmt x`,
  whose bits (read by integer instructions, or stored and reloaded) are given by THREAD-BITS, with
  the reading EXT-FLOAT-BITS when `x` is not representable in `fmt`. A floating MMA
  (`kind::f16`, `kind::tf32`, `kind::f8f6f4`) is the exact dot product over `kind.k` elements read
  by `TcMma.elementBytes`, with A row `TcMma.operandRow`. An element of `kind::f8f6f4` has a value
  only for the 8-bit types E4M3 and E5M2 (the byte as that format). An MMA with a 6- or 4-bit
  operand type keeps `noRule` under every scope (EXT-TCFIG) and needs a dedicated
  assumption. A warp-level `mma` or `mma.sp` whose element types are in `warpMma` has each D
  element the exact sum of the products of its A and B elements plus C (`idealWarpMma`,
  DEP-WARP-MMA). MMA, warp-level MMA and atomic or reduction elements are read by `valFloat`
  (THREAD-NUM), so an infinite or NaN element is `badValue`. A `.tf32` element is read by
  `tf32Value`, and an MMA with an `.f64` element keeps `noRule`: the assumption gives `.f64`
  elements no value, although `.f64` is a payload format (THREAD-BITS). The statement is generated
  from the scope and lists every form it covers.

Review: Rounding modes, overflow and subnormal handling are not represented. The forms that keep
  their rounding modifier (`sub`, and `add`, `sub`, `fma` of `.f32x2`) have a `FloatForm` only for
  `.rn` (`FloatForm.ofOp`): a directed rounding (`.rz`, `.rm`, `.rp`) is used by programs for the
  rounding itself (adding `1.5 * 2^23` with `.rm` rounds the other operand down to an integer),
  which an exact sum would erase, so such forms (`add.rm.f32x2`) are no `FloatForm` and need a
  dedicated assumption or the Core rule. This is a specification of the ideal computation. It
  makes no equality claim about GPU floating results. Approximate code must be reinterpreted by a
  dedicated assumption (ASM-APPROX, ASM-SEGMENT).

### OPEN-NUM — ideal arithmetic and hardware error

Statement: Under ASM-IDEAL and ASM-APPROX, a kernel's results are those of the exact real
  computation. How far the hardware's results can be from them is a separate numerical question
  that the model leaves open.

Effect: Results are the ideal real computation for the forms a kernel's assumptions name.

Review: Hardware rounding-error bounds remain a separate numerical proof obligation.
-/

def floatFmtText : FloatFmt → String
  | .f16 => "f16" | .bf16 => "bf16" | .f32 => "f32" | .f64 => "f64" | .e4m3 => "e4m3"
  | .e5m2 => "e5m2"

/-- A decoded floating instruction form: one per `Op` constructor and format, and only `.rn`
for the constructors that keep their rounding modifier. -/
inductive FloatForm where
  /-- `add{.rnd}{.ftz}.<fmt>` -/
  | add (fmt : FloatFmt)
  /-- `mul{.rnd}{.ftz}.<fmt>` -/
  | mul (fmt : FloatFmt)
  /-- `neg{.ftz}.<fmt>` on one lane. -/
  | neg (fmt : FloatFmt)
  /-- `fma.rnd{.ftz}.<fmt>` -/
  | fma (fmt : FloatFmt)
  /-- `mul{.rnd}{.ftz}.f32x2` -/
  | mulF32x2
  /-- `sub{.rn}{.ftz}.<fmt>`: round to nearest, written or by default; other roundings are no
  form. -/
  | subRn (fmt : FloatFmt)
  /-- `add{.rn}{.ftz}.f32x2` -/
  | addRnF32x2
  /-- `sub{.rn}{.ftz}.f32x2` -/
  | subRnF32x2
  /-- `fma.rn{.ftz}.f32x2` -/
  | fmaRnF32x2
  /-- `min{.ftz}.<fmt>` with two or three sources -/
  | min (fmt : FloatFmt)
  /-- `max{.ftz}.<fmt>` with two or three sources -/
  | max (fmt : FloatFmt)
  /-- `setp.CmpOp{.ftz}.<fmt>`, ordered and unordered `CmpOp`, with no infinite constant
  operand -/
  | setp (fmt : FloatFmt)
  /-- `setp.CmpOp{.ftz}.<fmt>` with an infinite constant operand (`0fFF800000`, `0f7F800000`) -/
  | setpInf (fmt : FloatFmt)
  /-- `cvt.f32.f16` -/
  | cvtF32F16
  /-- `cvt.rn.f16x2.f32` -/
  | cvtRnF16x2F32
  deriving DecidableEq, Repr

/-- A `0f` constant that encodes an infinity: `0fFF800000` or `0f7F800000`. -/
def isInfConst : Opnd → Bool
  | .f32imm b => b == 0xFF800000 || b == 0x7F800000
  | _ => false

/-- The `FloatForm` of a decoded instruction: the forms the decoder produced before the floating
family was decoded in full, now stated for every scalar format. `add`, `mul` and `fma` cover
every rounding modifier, `sub` and the `.f32x2` `add`, `sub` and `fma` only `.rn` (written or, for
`add` and `sub`, by default); none of them with `.sat`, a mixed source type, `.relu` or `.oob`. -/
def FloatForm.ofOp : Op → Option FloatForm
  | .float f =>
    let scalar := f.ty.lanes == 1 && f.srcTys.isEmpty
    let pair := f.ty == ⟨.f32, 2⟩ && f.srcTys.isEmpty
    let rn := f.rnd == none || f.rnd == some .rn
    match f.op with
    | .add => if scalar && !f.sat then some (.add f.ty.fmt)
      else if pair && rn then some .addRnF32x2 else none
    | .mul => if scalar && !f.sat then some (.mul f.ty.fmt)
      else if pair then some .mulF32x2 else none
    | .neg => if scalar && !f.sat then some (.neg f.ty.fmt) else none
    | .fma => if scalar && !f.sat && !f.relu && !f.oob then some (.fma f.ty.fmt)
      else if pair && f.rnd == some .rn then some .fmaRnF32x2 else none
    | .sub => if scalar && !f.sat && rn then some (.subRn f.ty.fmt)
      else if pair && rn then some .subRnF32x2 else none
    | .min | .max =>
      if scalar && !f.nanMod && !f.xorsign && !f.absMod then
        some (if f.op == .max then .max f.ty.fmt else .min f.ty.fmt)
      else none
    | .setp (.ord _) none | .setp (.unord _) none =>
      if f.ty.lanes == 1 && f.dsts.length == 1 then
        some (if f.srcs.any isInfConst then .setpInf f.ty.fmt else .setp f.ty.fmt)
      else none
    | _ => none
  | .cvt c => if c.widenF16?.isSome then some .cvtF32F16
    else if c.packF16?.isSome then some .cvtRnF16x2F32 else none
  | _ => none

def FloatForm.text : FloatForm → String
  | .add fmt => s!"add\{.rnd}\{.ftz}.{floatFmtText fmt}"
  | .mul fmt => s!"mul\{.rnd}\{.ftz}.{floatFmtText fmt}"
  | .neg fmt => s!"neg\{.ftz}.{floatFmtText fmt}"
  | .fma fmt => s!"fma.rnd\{.ftz}.{floatFmtText fmt}"
  | .mulF32x2 => "mul{.rnd}{.ftz}.f32x2"
  | .subRn fmt => s!"sub\{.rn}\{.ftz}.{floatFmtText fmt}"
  | .addRnF32x2 => "add{.rn}{.ftz}.f32x2"
  | .subRnF32x2 => "sub{.rn}{.ftz}.f32x2"
  | .fmaRnF32x2 => "fma.rn{.ftz}.f32x2"
  | .min fmt => s!"min\{.ftz}.{floatFmtText fmt} (two or three sources)"
  | .max fmt => s!"max\{.ftz}.{floatFmtText fmt} (two or three sources)"
  | .setp fmt => s!"setp.CmpOp\{.ftz}.{floatFmtText fmt} (ordered and unordered CmpOp)"
  | .setpInf fmt => s!"setp.CmpOp\{.ftz}.{floatFmtText fmt} with an infinite constant operand \
    (0fFF800000 or 0f7F800000), as the comparison of the exact real with that infinity"
  | .cvtF32F16 => "cvt.f32.f16"
  | .cvtRnF16x2F32 => "cvt.rn.f16x2.f32"

def f8f6f4Text : TcMma.F8f6f4 → String
  | .e4m3 => "e4m3" | .e5m2 => "e5m2" | .e2m3 => "e2m3" | .e3m2 => "e3m2" | .e2m1 => "e2m1"

def mmaKindText : TcMma.Kind → String
  | .f16 input output =>
    s!"tcgen05.mma kind::f16 ({floatFmtText input} inputs, {floatFmtText output} D)"
  | .tf32 => "tcgen05.mma kind::tf32"
  | .i8 .. => "tcgen05.mma kind::i8"
  | .f8f6f4 a b output =>
    s!"tcgen05.mma kind::f8f6f4 ({f8f6f4Text a} A, {f8f6f4Text b} B, {floatFmtText output} D)"

def rmwText (r : AtomOp × DType) : String :=
  let op := match r.1 with
    | .add => "add" | .min => "min" | .max => "max" | .inc => "inc" | .dec => "dec"
    | .and => "and" | .or => "or" | .xor => "xor" | .exch => "exch" | .cas => "cas"
  let ty := match r.2 with
    | .float .f16 => "f16" | .float .bf16 => "bf16" | .float .f32 => "f32" | .float .f64 => "f64"
    | _ => "other"
  s!"atom, red and tensor reduction .{op} of .{ty} elements"

/-- What an ideal-real assumption covers: floating instruction forms, MMA kinds and the elements
of `atom`, `red` and tensor reductions (operation, element type). -/
structure IdealScope where
  float : List FloatForm := []
  mma : List TcMma.Kind := []
  rmw : List (AtomOp × DType) := []
  /-- Warp-level `mma` and `mma.sp` element types (DEP-WARP-MMA). -/
  warpMma : List MmaTypes := []

/-- The text of a data type of a warp-level MMA. -/
def dtypeText : DType → String
  | .float .f16 => "f16" | .float .bf16 => "bf16" | .float .tf32 => "tf32"
  | .float .f32 => "f32" | .float .f64 => "f64" | .float .e4m3 => "e4m3"
  | .float .e5m2 => "e5m2" | _ => "other"

/-- The text of the element types of a warp-level MMA. -/
def warpMmaText (t : MmaTypes) : String :=
  s!"mma.sync and mma.sp ({dtypeText t.a} A, {dtypeText t.b} B, {dtypeText t.c} C, \
    {dtypeText t.d} D)"

def IdealScope.text (s : IdealScope) : String :=
  ", ".intercalate (s.float.map FloatForm.text ++ s.mma.map mmaKindText ++
    s.rmw.map rmwText ++ s.warpMma.map warpMmaText)

/-- A floating operand of format `fmt` in the extended reals: a payload of `fmt` is its number, and
every other value is the datum `classify` reads (THREAD-NUM), either zero being `0` and an
infinity `⊥` or `⊤`. A NaN gives `none`: the assumption declines and the Core rule applies. A
value of another width or without a bit pattern is a fault, as in THREAD-NUM. -/
def readEReal (fmt : FloatFmt) (v : Value) : Option (Exec EReal) :=
  match v with
  | .float f x => if f = fmt then some (pure (x : EReal)) else ofDatum (classify fmt v)
  | v => ofDatum (classify fmt v)
where
  ofDatum : Exec FVal → Option (Exec EReal)
    | .error e => some (.error e)
    | .ok (.zero _) => some (pure 0)
    | .ok (.fin q) => some (pure ((q : ℝ) : EReal))
    | .ok (.inf neg) => some (pure (if neg then ⊥ else ⊤))
    | .ok (.nan _) => none

/-- A floating operand of format `fmt` in the extended reals (`readEReal`): a register, or a `0f`
constant read as its 32-bit pattern. -/
def readERealOpnd (t : TState) (fmt : FloatFmt) : Opnd → Option (Exec EReal)
  | .reg r => match readReg t r with
    | .ok v => readEReal fmt v
    | .error e => some (.error e)
  | .f32imm b => readEReal fmt (.bits 32 (BitVec.ofNat 64 b))
  | _ => some (.error .typeMismatch)

/-- The two `.f32` elements of a `.f32x2` operand in the extended reals, low half first (§9.7.3:
"fA[0] = a[0:31]; fA[1] = a[32:63];"); `none` when either is NaN. -/
def readERealPair (L : Launch) (g : Nat) (t : TState) (o : Opnd) :
    Option (Exec (EReal × EReal)) :=
  match readValue L g t 64 o with
  | .error e => some (.error e)
  | .ok v =>
    let (v0, v1) := splitValue 64 v
    match readEReal .f32 v0, readEReal .f32 v1 with
    | some (.ok x0), some (.ok x1) => some (pure (x0, x1))
    | some (.error e), _ => some (.error e)
    | some (.ok _), some (.error e) => some (.error e)
    | _, _ => none

/-- The extended-real sum; `none` for `⊤ + ⊥` and `⊥ + ⊤`, which have no extended-real value. -/
def addEReal (x y : EReal) : Option EReal :=
  if (x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤) then none else some (x + y)

/-- The extended-real product; `none` for `0 · ±∞` and `±∞ · 0`. -/
def mulEReal (x y : EReal) : Option EReal :=
  if (x = 0 ∧ (y = ⊤ ∨ y = ⊥)) ∨ (y = 0 ∧ (x = ⊤ ∨ x = ⊥)) then none else some (x * y)

/-- An extended real as a result of format `fmt`: a real is the payload of its number, an
infinity the bits of that infinity (`FVal.toValue`). -/
def erealValue (fmt : FloatFmt) (x : EReal) : Value :=
  if x = ⊤ then (FVal.inf false).toValue fmt
  else if x = ⊥ then (FVal.inf true).toValue fmt
  else .float fmt x.toReal

/-- A comparison in the extended reals; there is no NaN, so ordered and unordered agree. -/
def erealCompare (cmp : Cmp) (x y : EReal) : Bool :=
  match cmp with
  | .eq => decide (x = y) | .ne => decide (x ≠ y) | .lt | .lo => decide (x < y)
  | .le | .ls => decide (x ≤ y) | .gt | .hi => decide (x > y) | .ge | .hs => decide (x ≥ y)

/-- Sequence two optional faulting reads: `none` (a declined operand) wins over a later fault only
when it comes first. -/
def bindRead {α β : Type} (x : Option (Exec α)) (k : α → Option (Exec β)) : Option (Exec β) :=
  match x with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok a) => k a

/-- Floating-point arithmetic, comparisons and conversions of the forms `FloatForm.ofOp` selects,
over the extended reals, whatever the rounding modifier. Each operand is read by `readEReal`. The
rule declines (`none`) on a NaN operand and on `∞ - ∞` and `0 · ∞`, so the Core rule applies
there. A real result is a payload, an infinite result the bits of that infinity. -/
def execIdealFloat (L : Launch) (g : Nat) (t : TState) : Op → Option (Exec TState)
  | .float f =>
    let fmt := f.ty.fmt
    let put (d : Nat) (v : Value) : Exec TState := pure (next (setReg t d v))
    match f.op, f.ty.lanes, f.dsts, f.srcs with
    | .add, 1, [some d], [a, b] =>
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        (addEReal x y).map fun r => put d (erealValue fmt r)
    | .sub, 1, [some d], [a, b] =>
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        (addEReal x (-y)).map fun r => put d (erealValue fmt r)
    | .mul, 1, [some d], [a, b] =>
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        (mulEReal x y).map fun r => put d (erealValue fmt r)
    | .neg, 1, [some d], [a] =>
      bindRead (readERealOpnd t fmt a) fun x => some (put d (erealValue fmt (-x)))
    | .fma, 1, [some d], [a, b, c] =>
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        bindRead (readERealOpnd t fmt c) fun z =>
          ((mulEReal x y).bind fun p => addEReal p z).map fun r => put d (erealValue fmt r)
    | .min, 1, [some d], a :: b :: c | .max, 1, [some d], a :: b :: c =>
      let pick := fun u v : EReal => if f.op == .max then max u v else min u v
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        match c with
        | [] => some (put d (erealValue fmt (pick x y)))
        | [c] => bindRead (readERealOpnd t fmt c) fun z =>
          some (put d (erealValue fmt (pick (pick x y) z)))
        | _ => some (throw .noRule)
    | .setp (.ord cmp) _, 1, [some d], [a, b] | .setp (.unord cmp) _, 1, [some d], [a, b] =>
      bindRead (readERealOpnd t fmt a) fun x => bindRead (readERealOpnd t fmt b) fun y =>
        some (put d (.pred (erealCompare cmp x y)))
    | .add, 2, [some d], [a, b] | .sub, 2, [some d], [a, b] | .mul, 2, [some d], [a, b] =>
      let op : EReal → EReal → Option EReal := match f.op with
        | .add => addEReal
        | .sub => fun x y => addEReal x (-y)
        | _ => mulEReal
      bindRead (readERealPair L g t a) fun (x0, x1) =>
        bindRead (readERealPair L g t b) fun (y0, y1) =>
          match op x0 y0, op x1 y1 with
          | some r0, some r1 => some (put d (.pair (erealValue .f32 r0) (erealValue .f32 r1)))
          | _, _ => none
    | .fma, 2, [some d], [a, b, c] =>
      bindRead (readERealPair L g t a) fun (x0, x1) =>
        bindRead (readERealPair L g t b) fun (y0, y1) =>
          bindRead (readERealPair L g t c) fun (z0, z1) =>
            match (mulEReal x0 y0).bind (addEReal · z0), (mulEReal x1 y1).bind (addEReal · z1) with
            | some r0, some r1 => some (put d (.pair (erealValue .f32 r0) (erealValue .f32 r1)))
            | _, _ => none
    | _, _, _, _ => some (throw .noRule)
  | .cvt c => match c.widenF16?, c.packF16? with
    | some (d, a), _ => bindRead (readERealOpnd t .f16 a) fun x =>
      some (pure (next (setReg t d (erealValue .f32 x))))
    | none, some (d, a, b) =>
      bindRead (readERealOpnd t .f32 a) fun x => bindRead (readERealOpnd t .f32 b) fun y =>
        some (pure (next (setReg t d (.pair (erealValue .f16 y) (erealValue .f16 x)))))
    | none, none => some (throw .noRule)
  | _ => some (throw .noRule)

/-- Floating elements of `atom`, `red` and tensor reductions (THREAD-ATOMIC-OP), over the reals:
add, and min and max, of `.f16`, `.bf16` and `.f32` elements. -/
def idealRmw (op : AtomOp) (ty : DType) (old src : Value) : Option (Exec Value) :=
  let float : Option FloatFmt := match ty with
    | .float .f16 => some .f16 | .float .bf16 => some .bf16 | .float .f32 => some .f32 | _ => none
  match float, op with
  | some f, .add => some do
    let x ← valFloat f old; let y ← valFloat f src
    pure (.float f (x + y))
  | some f, .min => some do
    let x ← valFloat f old; let y ← valFloat f src
    pure (.float f (min x y))
  | some f, .max => some do
    let x ← valFloat f old; let y ← valFloat f src
    pure (.float f (max x y))
  | _, _ => none

/-- A TF32 operand element (EXT-TCTF32): the FP32 bit pattern of its 32-bit container
(THREAD-BITS) with the low 13 mantissa bits cleared. -/
def tf32Value (v : Value) : Exec ℝ :=
  match v.bitPattern with
  | some n =>
    if v.bytes = 4 then bitsAsFloat .f32 (.bits 32 (BitVec.ofNat 64 (n &&& 0xFFFFE000)))
    else throw .typeMismatch
  | none => throw .typeMismatch

/-- Logical operand arrays are row-major M×K and N×K, independently of their
physical shared-memory layout. Missing bytes never supply an implicit zero. An E4M3 or E5M2
element of `kind::f8f6f4` is its byte; a 6- or 4-bit element has no value here
(EXT-TCFIG). -/
def idealMmaElement (kind : TcMma.Kind) (op : TcMma.Operand) (bs : List (Option Byte))
    (row k : Nat) : Exec ℝ := do
  let v ← rebuild 1 (TcMma.elementBytes kind bs row k)
  match kind with
  | .f16 input _ => valFloat input v
  | .tf32 => tf32Value v
  | .i8 .. => throw .noRule
  | .f8f6f4 a b _ =>
    match (match op with | .a => a | .b => b) with
    | .e4m3 => valFloat .e4m3 v
    | .e5m2 => valFloat .e5m2 v
    | .e2m3 | .e3m2 | .e2m1 => throw .noRule

/-- Exact dot product of the first `n` contraction elements. Negation is per operand. -/
def idealMmaDot (d : TcMma.Descriptor) (a b : List (Option Byte))
    (row col : Nat) : Nat → Exec ℝ
  | 0 => pure 0
  | n + 1 => do
    let prior ← idealMmaDot d a b row col n
    let x ← idealMmaElement d.kind .a a row n
    let y ← idealMmaElement d.kind .b b col n
    pure (prior + (if d.negateA then -x else x) * (if d.negateB then -y else y))

/-- The enable-input-D predicate controls whether the old accumulator is consumed. -/
def idealMmaAccumulator (fmt : FloatFmt) (accumulate : Bool) (old : Option Value) : Exec ℝ :=
  if accumulate then
    match old with
    | some v => valFloat fmt v
    | none => throw .uninitialized
  else pure 0

/-- Ideal arithmetic only. The caller must establish the byte observations and, when
accumulating, the old D value through the execution's TMEM rules. Disabled accumulation
does not read D. Transposition is already reflected in operand-address selection; `.ws` with
M < 128 reads one A row per D lane (`TcMma.operandRow`). `kind::f16` and `kind::tf32` are
floating; integer kinds have exact Core arithmetic. -/
def execIdealMma (d : TcMma.Descriptor) (accumulate : Bool)
    (a b : List (Option Byte)) (old : Option Value) (row col : Nat) : Exec Value := do
  let output ← match d.kind with
    | .i8 .. => throw .noRule
    | .f16 _ output => pure output
    | .tf32 => pure .f32
    | .f8f6f4 _ _ output => pure output
  unless TcMma.Valid d ∧ row < d.m ∧ col < d.n ∧ a.length = TcMma.Operand.bytes .a d ∧
      b.length = TcMma.Operand.bytes .b d do throw .noRule
  let dot ← idealMmaDot d a b (TcMma.operandRow d row col) col d.kind.k
  let previous ← idealMmaAccumulator output accumulate old
  pure (.float output (dot + previous))

/-- A floating element of a warp-level MMA as a real: a `.tf32` element is its FP32 pattern with
the low 13 mantissa bits cleared (`tf32Value`), an element of a payload format its number
(THREAD-NUM); an `.f64` element has no value here. -/
def idealWarpElem (ty : DType) (v : Value) : Exec ℝ :=
  match ty with
  | .float .tf32 => tf32Value v
  | .float .f64 => throw .noRule
  | .float f => match f.fmt? with
    | some fmt => valFloat fmt v
    | none => throw .noRule
  | _ => throw .noRule

/-- One D element of a warp-level floating MMA over the reals (DEP-WARP-MMA): the exact sum of
the products of the A and B elements plus C, as a payload of D's format; an `.f64` D has none. -/
def idealWarpMma (t : MmaTypes) (as bs : List Value) (c : Value) : Option (Exec Value) :=
  match t.d with
  | .float .f64 => none
  | .float f => f.fmt?.map fun fmt => do
    let ps ← (as.zip bs).mapM fun (x, y) => do
      pure ((← idealWarpElem t.a x) * (← idealWarpElem t.b y))
    let z ← idealWarpElem t.c c
    pure (.float fmt (ps.sum + z))
  | _ => none

/-- The ideal-real assumption for exactly the forms in `s`; `why` says why the kernel needs
it. Neither execution filtering nor safety assumptions. -/
def idealReal (name : String) (s : IdealScope) (why : String) : Assumption where
  name := name
  statement := s!"Exact real arithmetic for exactly these forms: {s.text}. Results are not \
    rounded, do not overflow and are never subnormal, and zero has no sign (a zero result is +0). \
    For the floating instruction forms an infinite operand is read as that infinity, and an \
    operation with a NaN operand, ∞ − ∞ or 0 × ∞ takes the Core rule; MMA, warp-level MMA and \
    atomic or reduction elements must be finite numbers. {why}"
  localRule L g t op := match FloatForm.ofOp op with
    | some f => if f ∈ s.float then execIdealFloat L g t op else none
    | none => none
  mmaRule d acc a b old row col :=
    if d.kind ∈ s.mma then some (execIdealMma d acc a b old row col) else none
  rmwRule op ty old src := if (op, ty) ∈ s.rmw then idealRmw op ty old src else none
  matrixMmaRule t as bs c := if t ∈ s.warpMma then idealWarpMma t as bs c else none

end
end PTX.Assumption
