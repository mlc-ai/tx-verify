-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Round
public import Core.Isa.Float
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# IEEE 754 operations

The special-value table of the floating instructions that support rounding modifiers, `.ftz`,
`.sat`, `.relu` and `.oob`, and the instructions that the manual defines by their text: `neg`,
`abs`, `copysign`, `min`, `max`, `testp` and the comparisons of `setp` and `set`.
-/

namespace PTX

noncomputable section

/-! ## THREAD-FLOAT-IEEE — IEEE 754 operations and the instructions defined by their text
Statement: An instruction with a rounding modifier computes the exact result of its operands in
  the extended reals and rounds it to the destination format by IEEE 754, with the IEEE 754 rules
  for NaN, invalid operations and the sign of an exact zero (EXT-IEEE754); a NaN result has
  unspecified bits. `neg`, `abs`, `copysign`, `min`, `max`, `testp`, `setp` and `set` follow the
  text and the Semantics pseudocode of their sections.

Defs: FVal.isNaN, FVal.isNeg, FVal.toRat, FVal.signBit, FVal.withSign, FVal.negate, FVal.absV,
  FVal.subnormalIn, FVal.add, FVal.mul, FVal.div, Layout.roundFtz, Layout.roundVal, Layout.sqrt,
  FVal.sat, FVal.relu, FVal.lt, FVal.minMax, minMaxOp, FVal.copysign, Cmp.evalF, FCmp.eval,
  TestProp.eval, FloatInstr.srcFmt, FloatInstr.flushIn, FloatInstr.arith, FloatInstr.ieee,
  FloatInstr.compare

Source:
- §9.7.3: "Instructions that support rounding modifiers are IEEE-754 compliant."
- §9.7.3: "Single-precision instructions return an unspecified NaN"
- §9.7.4: "Half-precision instructions return an unspecified NaN ."
- §9.7.3: "NaN payloads are supported for double-precision instructions (except for
    rcp.approx.ftz.f64 and rsqrt.approx.ftz.f64 , which maps input NaN s to a canonical NaN )."
- §9.7.3: "The optional .ftz modifier on single-precision instructions provides backward
    compatibility with sm_1x targets by flushing subnormal inputs and results to sign-preserving
    zero regardless of the target architecture"
- §9.7.3: "If no rounding modifier is specified, default is .rn and instructions may be folded
    into a multiply-add."
- §9.7.3.3: "In particular, mul / add sequences with no rounding modifiers may be optimized to use
    fused-multiply-add instructions on the target device"
- §9.7.3.6: "fma.f32 computes the product of a and b to infinite precision and then adds c to this
    product, again in infinite precision"
- §9.7.3.7: "mad.{f32,f64} is the same as fma.{f32,f64}"
- §9.7.3.8: "Divide with IEEE 754 compliant rounding:"
- §9.7.3.13: "Reciprocal with IEEE 754 compliant rounding:"
- §9.7.3.15: "Square root with IEEE 754 compliant rounding:"
- §9.7.3.3: "Saturation modifier: add.sat.f32 clamps the result to [0.0, 1.0]."
- §9.7.3.3: "NaN results are flushed to +0.0f ."
- §9.7.4.4: "fma.relu.{f16, f16x2, bf16, bf16x2} clamps the result to 0 if negative"
- §9.7.4.4: "NaN result is converted to canonical NaN"
- §9.7.4.4: "Out Of Bounds modifier: fma.oob.{f16, f16x2, bf16, bf16x2} clamps the result to 0 if
    either of the operands is OOB NaN (defined under Tensors ) value"
- §9.7.5: "Before executing the specified operation, operands with different precision needs to
    be converted such that all the instruction operands can be represented with a consistent
    floating-point precision"
- §9.7.5.1: "d[0:15] = convert(a[0:31] + c[0:31]); // Apply rz for output"
- §9.7.5.4: "d[0:15] = convert(a[0:31] * c[0:31]); // Apply rz for output"
- §9.7.3.10: "Negate the sign of a and store the result in d ."
- §9.7.3.10: "NaN inputs yield an unspecified NaN"
- §9.7.3.9: "Take the absolute value of a and store the result in d ."
- §9.7.3.9: "For abs.f32 , NaN input yields unspecified NaN"
- §9.7.3.9: "For abs.f64 , NaN input is passed through unchanged"
- §9.7.3.2: "Copy sign bit of a into value of b , and return the result as d ."
- §9.7.3.1: "testp.finite True if the input is not infinite or NaN testp.infinite True if the input
    is positive or negative infinity testp.number True if the input is not NaN testp.notanumber
    True if the input is NaN testp.normal True if the input is a normal number (not NaN , not
    infinity) testp.subnormal True if the input is a subnormal number (not NaN , not infinity) As
    a special case, positive and negative zero are considered normal numbers."
- §9.7.3.11: "def min_num (z, x, y) { if (isNaN(x) && isNaN(y)) z = NaN; else if (isNaN(x)) z = y;
    else if (isNaN(y)) z = x; else // note: -0.0 < +0.0 here z = (x < y) ? x : y; return z; }"
- §9.7.3.11: "def min_nan (z, x, y) { if (isNaN(x) || isNaN(y)) z = NaN; else // note: -0.0 < +0.0
    here z = (x < y) ? x : y; return z; }"
- §9.7.3.11: "if (.xorsign && !isPresent(c)) { xorsign = getSignBit(a) ^ getSignBit(b); } if (.abs)
    { a = |a|; b = |b|; if (isPresent(c)) { c = |c|; } } d = two_inputs_min(d, a, b) if
    (isPresent(c)) { d = two_inputs_min(d, d, c) } if (.xorsign && !isPresent(c) && !isNaN(d)) {
    setSignBit(d, xorsign); }"
- §9.7.3.11: "If the result of min is NaN then the .xorsign and .abs modifiers will be ignored"
- §9.7.3.11: "If values of both inputs are 0.0, then +0.0 > -0.0."
- §9.7.3.12: "if (.xorsign && !isPresent(c) !isNaN(d)) { setSignBit(d, xorsign); }"
- §9.7.4.8: "if (.xorsign && !isNaN(fA[i])) { setSignBit(d[i], xorsign); }"
- §9.7.4.8: "If the result of max is NaN then the .xorsign and .abs modifiers will be ignored."
- §9.3.1.2: "If either operand is NaN , the result is False ."
- §9.3.1.2: "If both operands are numeric values (not NaN ), then the comparison has the same result
    as its ordered counterpart. If either operand is NaN , then the result of the comparison is
    True ."
- §9.3.1.2: "num returns True if both operands are numeric values (not NaN ), and nan returns True
    if either operand is NaN ."
- §9.7.7.2: "setp.ftz.dtype.f32 flushes subnormal inputs to sign-preserving zero."
- §9.7.7.2: "Modifier .ftz applies only to .f32 comparisons."
- EXT-IEEE754

Direction: stricter

Applies: The floating instructions whose rule is THREAD-FLOAT and whose mode is not `.approx`

Premises: The sources are read as data of their formats (THREAD-FLOAT).

Effect: Local evaluation. `FloatInstr.arith` computes `add`, `sub`, `mul`, `fma`, `mad` (the rule
  of `fma`), `div`, `rcp` (`1 / a`) and `sqrt` exactly and rounds by the written modifier with IEEE
  754 overflow (`Layout.round`, THREAD-FLOAT-ROUND). A NaN operand, `∞ − ∞`, `0 × ∞`, `0 / 0`, `∞ /
  ∞` and the square root of a negative number give a NaN whose bits are unknown; the manual names no
  payload for these results, `.f64` included. An exact zero sum is `-0` when both operands are
  `-0`, `+0` when both are `+0`, and otherwise `+0` except under `.rm`, which gives `-0` (IEEE 754
  §6.3); a zero product or quotient has the XOR of the operand signs. An `add`, `sub` or `mul`
  without a written rounding modifier has no rule, since the code optimizer may fuse it with a
  neighbouring instruction and the result then depends on another instruction. `.ftz` flushes
  every subnormal input and result to the zero of its sign; the manual does not say whether a
  result is tested before or after rounding, so an exact result below the smallest normal
  magnitude that rounds to a normal number has no rule (`Layout.roundFtz`). `.relu` makes a
  negative result `+0` and a NaN result an opaque NaN; `.sat` makes a NaN result `+0` and clamps
  to `[0.0, 1.0]`; both are applied after the flush, and under both a `-0` result has no rule,
  since the manual does not say whether the clamp keeps the sign of zero. `.oob` has no rule with
  a NaN operand, since the manual gives no encoding of the OOB-NaN, and no effect otherwise. A
  mixed-precision form computes on its operands in their own formats, which converts each of them
  exactly to `.f32`, and rounds once to the destination format; for the `.rz` forms to `.bf16x2`
  and `.f16x2` this equals the rounding to `.f32` followed by the rounding to the destination,
  since rounding toward zero twice through a finer grid equals rounding once. The forms to
  `.f16x2` carry `.ftz` without a subnormal sentence, so they have a rule only when no input is
  subnormal in its format and the result is not subnormal, where flushing and not flushing agree.
  `neg` flips and `abs` clears the sign of a datum after the `.ftz` flush; a NaN input gives an
  opaque NaN, except that `abs.f64` passes it through. `copysign` gives `b` with the sign bit of
  `a`; an opaque NaN `a` gives no rule unless `b` is an opaque NaN too. `min` and `max` follow the
  Semantics pseudocode, with `-0` below `+0`; a NaN result is opaque; `.xorsign` uses the sign bit
  of a NaN operand when its pattern is known and has no rule when it is unknown. The `.f32` `max`
  pseudocode lacks an operator in `!isPresent(c) !isNaN(d)`, which is read as `&&` as in `min`.
  The `.f16x2` and `.bf16x2` `max` pseudocode applies `.xorsign` when `fA[i]` is not NaN, while the
  description ignores `.xorsign` only for a NaN result, so a lane whose `fA[i]` is NaN and whose
  result is not NaN has no rule under `.xorsign`. A comparison compares the numbers of its
  operands in the extended reals, both zeros denoting `0`, with Tables 23 to 25 for NaN; `lo`,
  `ls`, `hi` and `hs` have no floating rule. `testp` classifies its operand, an opaque NaN being
  `notanumber` and both zeros normal.

### EXT-IEEE754 — the IEEE 754 rules of the instructions with rounding modifiers

Statement: An instruction with a rounding modifier computes the exact result of its operands and
  rounds it as IEEE 754 specifies: the rounding-direction attributes, the arithmetic of infinity
  and NaN, the sign of an exact zero result, invalid operations and overflow per rounding
  direction. The sentences of the manual that override IEEE 754 (`.ftz`, `.sat`, `.relu`,
  `.satfinite`, the unspecified NaN) take precedence.

Why it is not spec text: The manual states "Instructions that support rounding modifiers are
  IEEE-754 compliant." and, for `fma`, "fma.f32 computes the product of a and b to infinite
  precision and then adds c to this product, again in infinite precision", without restating the
  IEEE 754 rules it imports. The model takes them from IEEE 754-2008 and IEEE 754-2019, which agree
  on every rule used here (§4.3 rounding-direction attributes, §6.1 and §6.2 infinity and NaN
  arithmetic, §6.3 the sign bit, §7.2 invalid operation, §7.4 overflow).

Effect: The special values, the zero signs and the rounded results of THREAD-FLOAT-IEEE,
  THREAD-FLOAT-ROUND and THREAD-CVT follow these rules; if the hardware deviates from IEEE 754 in a
  case the manual does not mention, the proven results differ from the hardware's. Disclosed by
  every kernel whose statement names `Op.float` or `Op.cvt`: BlockSum, FlashAttn4Fwd,
  FlashMlaSparseDecodeH64, Fp16Gemm8192, InklingRelDecode, RmsNorm, RowSum.
-/

/-- Whether a datum is NaN. -/
def FVal.isNaN : FVal → Bool
  | .nan _ => true
  | _ => false

/-- The sign of a zero, a number or an infinity; `false` for NaN. -/
def FVal.isNeg : FVal → Bool
  | .zero s | .inf s => s
  | .fin x => decide (x < 0)
  | .nan _ => false

/-- The number of a zero or a finite datum; `0` for an infinity and NaN. -/
def FVal.toRat : FVal → ℚ
  | .fin x => x
  | _ => 0

/-- The sign bit of a datum of layout `L`: for a NaN with a known pattern the top bit of the
pattern; an opaque NaN has none. -/
def FVal.signBit (L : Layout) : FVal → Option Bool
  | .nan (some n) => some (n / 2 ^ (L.width - 1) % 2 == 1)
  | .nan none => none
  | v => some v.isNeg

/-- The datum of layout `L` with sign bit `s`: the same magnitude, or for a NaN with a known
pattern the pattern with its top bit set to `s`. An opaque NaN stays opaque. -/
def FVal.withSign (L : Layout) (s : Bool) : FVal → FVal
  | .zero _ => .zero s
  | .fin x => .fin (if s then -|x| else |x|)
  | .inf _ => .inf s
  | .nan (some n) =>
    .nan (some (n % 2 ^ (L.width - 1) + if s then 2 ^ (L.width - 1) else 0))
  | .nan none => .nan none

/-- The negation of a datum; a NaN gives an opaque NaN. -/
def FVal.negate : FVal → FVal
  | .zero s => .zero !s
  | .fin x => .fin (-x)
  | .inf s => .inf !s
  | .nan _ => .nan none

/-- The absolute value of a datum; a NaN gives an opaque NaN. -/
def FVal.absV : FVal → FVal
  | .zero _ => .zero false
  | .fin x => .fin |x|
  | .inf _ => .inf false
  | .nan _ => .nan none

/-- Whether a datum is a subnormal number of layout `L`. -/
def FVal.subnormalIn (L : Layout) : FVal → Bool
  | .fin x => L.subnormal x
  | _ => false

/-- The exact sum in the extended reals under rounding mode `m`, unrounded: a NaN operand and
`∞ − ∞` give an opaque NaN, and an exact zero sum has the sign of IEEE 754 §6.3, which depends on
whether the mode is `.rm`. -/
def FVal.add (m : RoundMode) : FVal → FVal → FVal
  | .nan _, _ | _, .nan _ => .nan none
  | .inf s, .inf t => if s = t then .inf s else .nan none
  | .inf s, _ | _, .inf s => .inf s
  | a, b =>
    let q := a.toRat + b.toRat
    if q = 0 then
      .zero (if a.toRat = 0 ∧ b.toRat = 0 ∧ a.isNeg = b.isNeg then a.isNeg else m = .rm)
    else .fin q

/-- The exact product in the extended reals, unrounded: a NaN operand and `0 × ∞` give an opaque
NaN, and every other zero or infinite product has the XOR of the operand signs. -/
def FVal.mul : FVal → FVal → FVal
  | .nan _, _ | _, .nan _ => .nan none
  | .inf _, .zero _ | .zero _, .inf _ => .nan none
  | .inf s, b | b, .inf s => .inf (s != b.isNeg)
  | a, b =>
    let q := a.toRat * b.toRat
    if q = 0 then .zero (a.isNeg != b.isNeg) else .fin q

/-- The exact quotient in the extended reals, unrounded: a NaN operand, `0 / 0` and `∞ / ∞` give
an opaque NaN, a nonzero number or an infinity divided by zero and an infinity divided by a number
give an infinity, and a number divided by an infinity gives a zero, each with the XOR of the
operand signs. -/
def FVal.div : FVal → FVal → FVal
  | .nan _, _ | _, .nan _ => .nan none
  | .zero _, .zero _ | .inf _, .inf _ => .nan none
  | a, .zero s => .inf (a.isNeg != s)
  | .inf s, b => .inf (s != b.isNeg)
  | a, .inf s => .zero (a.isNeg != s)
  | a, b =>
    let q := a.toRat / b.toRat
    if q = 0 then .zero (a.isNeg != b.isNeg) else .fin q

open Classical in
/-- The rounding of a nonzero exact real `r` to layout `L` by mode `m` with IEEE 754 overflow,
followed by the `.ftz` flush of the result when `ftz` is set. With `.ftz`, an `r` below the
smallest normal magnitude whose rounding is a normal number has no rule, since the manual does not
say whether the result is tested for a subnormal before or after rounding. -/
def Layout.roundFtz (L : Layout) (m : RoundMode) (ftz : Bool) (r : ℝ) : Option FVal := do
  let v ← L.round m .inf r false
  if ftz then
    if |r| < ((L.minNormal : ℚ) : ℝ) ∧ (match v with | .fin y => !L.subnormal y | _ => false)
    then none
    else some (L.flush v)
  else some v

/-- The rounding of an exact datum to layout `L`: a finite number is rounded by
`Layout.roundFtz`, and every other datum is the result itself. -/
def Layout.roundVal (L : Layout) (m : RoundMode) (ftz : Bool) : FVal → Option FVal
  | .fin q => L.roundFtz m ftz q
  | v => some v

open Classical in
/-- The square root rounded to layout `L`: a NaN or a negative operand, `-∞` included, gives an
opaque NaN, a zero keeps its sign and `+∞` gives `+∞`. -/
def Layout.sqrt (L : Layout) (m : RoundMode) (ftz : Bool) : FVal → Option FVal
  | .fin x => if x < 0 then some (.nan none) else L.roundFtz m ftz (Real.sqrt x)
  | .inf true | .nan _ => some (.nan none)
  | v => some v

/-- `.sat`: a NaN gives `+0`, a number below `0` gives `+0` and one above `1.0` gives `1.0`; a
`-0` has no rule. -/
def FVal.sat : FVal → Option FVal
  | .nan _ | .inf true => some (.zero false)
  | .inf false => some (.fin 1)
  | .zero true => none
  | .zero false => some (.zero false)
  | .fin x => some (if x < 0 then .zero false else if 1 < x then .fin 1 else .fin x)

/-- `.relu`: a negative number gives `+0` and a NaN an opaque NaN; a `-0` has no rule. -/
def FVal.relu : FVal → Option FVal
  | .nan _ => some (.nan none)
  | .inf true => some (.zero false)
  | .zero true => none
  | .fin x => some (if x < 0 then .zero false else .fin x)
  | v => some v

/-- The order of non-NaN data in the extended reals; with `signedZero`, `-0` is below `+0`. -/
def FVal.lt (signedZero : Bool) (a b : FVal) : Bool :=
  let rank : FVal → Nat := fun
    | .inf true => 0
    | .inf false => 2
    | _ => 1
  decide (rank a < rank b) ||
    (rank a == 1 && rank b == 1 &&
      (decide (a.toRat < b.toRat) || (signedZero && a == .zero true && b == .zero false)))

/-- `min_num` and `min_nan` (`max_num` and `max_nan` when `isMax`) of the Semantics pseudocode:
two NaN inputs, or one under `.NaN`, give an opaque NaN; one NaN input gives the other input; two
numbers give the smaller (larger) one with `-0` below `+0`. -/
def FVal.minMax (isMax nanMod : Bool) (x y : FVal) : FVal :=
  if (x.isNaN && y.isNaN) || (nanMod && (x.isNaN || y.isNaN)) then .nan none
  else if x.isNaN then y
  else if y.isNaN then x
  else if (if isMax then FVal.lt true y x else FVal.lt true x y) then x
  else y

/-- `min` or `max` of the flushed inputs `x :: y :: rest` of one lane of layout `L`: `.abs` takes
the absolute values, the inputs are combined from the left, and `.xorsign` (two inputs only) gives
a non-NaN result the XOR of the sign bits of `x` and `y`. `packedMax` is `max` of a packed half
type, where a NaN `x` with a non-NaN result has no rule under `.xorsign`. -/
def minMaxOp (L : Layout) (isMax nanMod absMod xorsign packedMax : Bool) :
    List FVal → Option FVal
  | x :: y :: rest => do
    let ab (v : FVal) : FVal := if absMod then v.absV else v
    let d := (rest.map ab).foldl (FVal.minMax isMax nanMod) (FVal.minMax isMax nanMod (ab x) (ab y))
    if xorsign && rest.isEmpty && !d.isNaN then
      if packedMax && x.isNaN then none
      else
        let sx ← x.signBit L
        let sy ← y.signBit L
        some (d.withSign L (sx != sy))
    else some d
  | _ => none

/-- `copysign`: `b` with the sign bit of `a`. An opaque NaN `b` gives an opaque NaN; an opaque NaN
`a` has no rule otherwise. -/
def FVal.copysign (L : Layout) (a b : FVal) : Option FVal :=
  match b with
  | .nan none => some (.nan none)
  | _ => (a.signBit L).map fun s => b.withSign L s

/-- The ordered comparison of two non-NaN data in the extended reals (Table 23), both zeros being
`0`; `lo`, `ls`, `hi` and `hs` have none. -/
def Cmp.evalF : Cmp → FVal → FVal → Option Bool
  | .eq, a, b => some (!FVal.lt false a b && !FVal.lt false b a)
  | .ne, a, b => some (FVal.lt false a b || FVal.lt false b a)
  | .lt, a, b => some (FVal.lt false a b)
  | .le, a, b => some !(FVal.lt false b a)
  | .gt, a, b => some (FVal.lt false b a)
  | .ge, a, b => some !(FVal.lt false a b)
  | _, _, _ => none

/-- A floating comparison (Tables 23 to 25): an ordered comparison is false and an unordered one
true when an operand is NaN; `num` tests that neither and `nan` that one operand is NaN. -/
def FCmp.eval : FCmp → FVal → FVal → Option Bool
  | .ord c, a, b => if a.isNaN || b.isNaN then some false else c.evalF a b
  | .unord c, a, b => if a.isNaN || b.isNaN then some true else c.evalF a b
  | .num, a, b => some (!a.isNaN && !b.isNaN)
  | .nan, a, b => some (a.isNaN || b.isNaN)

/-- The property `testp` tests of a datum of layout `L`; both zeros are normal. -/
def TestProp.eval (L : Layout) : TestProp → FVal → Bool
  | .finite, v => match v with
    | .zero _ | .fin _ => true
    | _ => false
  | .infinite, v => match v with
    | .inf _ => true
    | _ => false
  | .number, v => !v.isNaN
  | .notanumber, v => v.isNaN
  | .normal, v => match v with
    | .zero _ => true
    | .fin x => !L.subnormal x
    | _ => false
  | .subnormal, v => v.subnormalIn L

/-- The format of source `i`: its entry of `srcTys` for a mixed-precision form, and the type
otherwise. -/
def FloatInstr.srcFmt (f : FloatInstr) (i : Nat) : FloatFmt :=
  ((f.srcTys[i]?).map (·.fmt)).getD f.ty.fmt

/-- The sources after the `.ftz` input flush, each in the layout of its own format. -/
def FloatInstr.flushIn (f : FloatInstr) (xs : List FVal) : List FVal :=
  if f.ftz then xs.mapIdx fun i x => (f.srcFmt i).layout.flush x else xs

/-- The arithmetic of one lane: `add`, `sub`, `mul`, `fma`, `mad`, `div`, `rcp` and `sqrt` with a
written rounding modifier, rounded to the destination format, then `.oob`, `.relu` and `.sat`. A
mixed-precision form with `.ftz` has a rule only when no input is subnormal in its format and the
result is not subnormal. -/
def FloatInstr.arith (f : FloatInstr) (xs : List FVal) : Option FVal := do
  let m ← f.rnd.map FloatRound.mode
  let L := f.ty.fmt.layout
  let mixedFtz := f.ftz && !f.srcTys.isEmpty
  guard !(mixedFtz && (xs.mapIdx fun i x => x.subnormalIn (f.srcFmt i).layout).any id)
  let ys := if mixedFtz then xs else f.flushIn xs
  let ftz := f.ftz && !mixedFtz
  let v ← match f.op, ys with
    | .add, [a, b] => L.roundVal m ftz (a.add m b)
    | .sub, [a, b] => L.roundVal m ftz (a.add m b.negate)
    | .mul, [a, b] => L.roundVal m ftz (a.mul b)
    | .fma, [a, b, c] | .mad, [a, b, c] => L.roundVal m ftz ((a.mul b).add m c)
    | .div, [a, b] => L.roundVal m ftz (a.div b)
    | .rcp, [a] => L.roundVal m ftz ((FVal.fin 1).div a)
    | .sqrt, [a] => L.sqrt m ftz a
    | _, _ => none
  guard !(mixedFtz && v.subnormalIn L)
  guard !(f.oob && xs.any FVal.isNaN)
  let v ← if f.relu then v.relu else some v
  if f.sat then v.sat else some v

/-- The value of one lane of a floating instruction that is not approximate: the arithmetic of
`FloatInstr.arith`, and `neg`, `abs`, `copysign`, `min` and `max` on the flushed sources. -/
def FloatInstr.ieee (f : FloatInstr) (xs : List FVal) : Option FVal :=
  let L := f.ty.fmt.layout
  let packedMax := f.op == .max && f.ty.lanes == 2
  match f.op, f.flushIn xs with
  | .add, _ | .sub, _ | .mul, _ | .fma, _ | .mad, _ | .div, _ | .rcp, _ | .sqrt, _ =>
    f.arith xs
  | .neg, [a] => some a.negate
  | .abs, [a] => some (if a.isNaN && f.ty.fmt = .f64 then a else a.absV)
  | .copysign, [a, b] => FVal.copysign L a b
  | .min, ys => minMaxOp L false f.nanMod f.absMod f.xorsign false ys
  | .max, ys => minMaxOp L true f.nanMod f.absMod f.xorsign packedMax ys
  | _, _ => none

/-- The Boolean of one lane of `testp`, `setp` or `set` with a floating source type: the class of
the operand, or the comparison of the flushed operands. -/
def FloatInstr.compare (f : FloatInstr) (xs : List FVal) : Option Bool :=
  match f.op, f.flushIn xs with
  | .testp p, [a] => some (p.eval f.ty.fmt.layout a)
  | .setp c _, [a, b] | .set c _ _, [a, b] => if f.cmpTy.isSome then none else c.eval a b
  | _, _ => none

end

end PTX
