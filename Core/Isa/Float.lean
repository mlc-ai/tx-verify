-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Int

@[expose] public section

/-!
# Floating-point instructions

The representation of the floating-point, half-precision and mixed-precision instructions and
its construction from a recognized instruction.
-/

namespace PTX

/-! ## PROG-ISA-FLOAT — floating-point instructions
Statement: A floating instruction is its operation, its type, the source types of a mixed-precision
  form, its rounding modifier as written, whether it is approximate, its `.ftz`, `.sat`, `.relu`,
  `.oob`, `.NaN`, `.xorsign` and `.abs` qualifiers, its destinations and its sources. Every entry of
  the `float` family decodes to it; operands are resolved at the widths of their table types.

Defs: TestProp, FCmp, FOp, FTy, FTy.ofDType?, FMode, FloatInstr, Decode.FloatInstr.cmp?,
  Decode.FloatInstr.fty, Decode.FloatInstr.ofRaw, FloatInstr.rule

Source:
- §9.7.3.3: "add{.rnd}{.ftz}{.sat}.f32 d, a, b; add{.rnd}{.ftz}.f32x2 d, a, b; add{.rnd}.f64 d, a,
    b;"
- §9.7.3.6: "fma.rnd{.ftz}{.sat}.f32 d, a, b, c; fma.rnd{.ftz}.f32x2 d, a, b, c; fma.rnd.f64 d, a,
    b, c;"
- §9.7.3.8: "div.approx{.ftz}.f32 d, a, b; // fast, approximate divide div.full{.ftz}.f32 d, a, b;
    // full-range approximate divide div.rnd{.ftz}.f32 d, a, b; // IEEE 754 compliant rounding"
- §9.7.3.11: "min{.ftz}{.NaN}{.xorsign.abs}.f32 d, a, b; min{.ftz}{.NaN}{.abs}.f32 d, a, b, c;
    min.f64 d, a, b;"
- §9.7.3.1: "testp.op.type p, a; // result is .pred .op = { .finite, .infinite, .number,
    .notanumber, .normal, .subnormal };"
- §9.7.7.1: "set.CmpOp{.ftz}.dtype.stype d, a, b; set.CmpOp.BoolOp{.ftz}.dtype.stype d, a, b,
    {!}c;"
- §9.7.4.4: "fma.rnd{.ftz}{.sat}.f16 d, a, b, c; fma.rnd{.ftz}{.sat}.f16x2 d, a, b, c;
    fma.rnd{.ftz}.relu.f16 d, a, b, c;"
- §9.7.5.1: "add{.rnd}{.sat}.cdtype.atype d, a, c; add{.rnd}.dtype2.atype2.ctype2 d, a, c;
    add.rz.ftz.dtype3.atype3.ctype2 d, a, c; add.rz.dtype4.atype3.ctype2 d, a, c;"
- §9.7.5.3: "fma{.rnd}{.sat}.cdtype.abtype d, a, b, c; fma{.rnd}.dtype.atype.btype.ctype d, a, b,
    c;"
- §9.7.5.4: "mul.ftz.rz.dtype1.atype1.ctype1 d, a, c; mul.rz.dtype2.atype1.ctype1 d, a, c;
    mul.dtype3.atype2.ctype2 d, a, c; mul.dtype4.atype3.ctype3 d, a, c;"
- §9.7.3: "mad.f32 and fma.f32 are the same."

Direction: representation

Applies: Every instruction of the `float` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `FloatInstr.rule` selects THREAD-FLOAT for every form except `div.full`, the
  mixed `fma` with a packed half `.atype` and the `mul` forms that mix `.f16x2` and `.bf16x2`, which
  have no rule. The rounding modifier is kept as written (`none` when omitted), since an omitted
  modifier lets the code optimizer contract `mul` and `add` (THREAD-FLOAT). `mad` is its own
  operation with the rule of `fma`. A mixed-precision form records the types of its sources in
  operand order (`srcTys`); every other form has `srcTys = []`. A `set` with an integer source type
  records it (`cmpTy`) and takes the destination format as its type. The model does not decode a
  negated predicate source `!c`, a comparison operator `lo`, `ls`, `hi` or `hs` with a floating
  source type, or `.relu` on a floating `min` or `max`, which the manual does not define; each fails
  decoding. A `0d` constant or a decimal floating literal does not decode either (`Opnd` holds `0f`
  constants only).
-/

/-- The property `testp` tests (§9.7.3.1). -/
inductive TestProp where
  | finite | infinite | number | notanumber | normal | subnormal
  deriving DecidableEq, Repr

/-- A floating comparison (§9.3.1.2, Tables 23 to 25): an ordered comparison, its unordered
counterpart, `num` or `nan`. -/
inductive FCmp where
  | ord (c : Cmp)
  | unord (c : Cmp)
  | num
  | nan
  deriving DecidableEq, Repr

/-- A floating operation (§9.7.3, §9.7.4, §9.7.5, §9.7.7, §9.7.8). -/
inductive FOp where
  | add | sub | mul | fma | mad | div | rcp | sqrt | rsqrt
  | ex2 | lg2 | sin | cos | tanh
  | abs | neg | min | max | copysign
  | testp (p : TestProp)
  | setp (c : FCmp) (bop : Option BoolOp)
  | set (c : FCmp) (bop : Option BoolOp) (dst : DType)
  deriving DecidableEq, Repr

/-- An element format and the number of elements in one register (1, or 2 for `x2`). -/
structure FTy where
  fmt : FloatFmt
  lanes : Nat := 1
  deriving DecidableEq, Repr

/-- The format and lane count of a floating or packed floating data type with a payload format. -/
def FTy.ofDType? : DType → Option FTy
  | .float f => f.fmt?.map fun fmt => ⟨fmt, 1⟩
  | .packed (.float f) n => f.fmt?.map fun fmt => ⟨fmt, n⟩
  | _ => none

/-- `.approx`, `.full` (`div` only) or a correctly rounded form. -/
inductive FMode where
  | ieee | approx | full
  deriving DecidableEq, Repr

/-- A floating instruction: the operation, its type (`.type`, the destination type of a mixed
form or of `set`, or the source type of `setp` and of a `set` with a floating source), the source
types of a mixed form in operand order (`[]` when every source has type `ty`), the integer source
type of a `set` with an integer `.stype`, the rounding modifier as written, the mode, the
qualifiers, the destinations (`none` for the sink `_`) and the sources in operand order. -/
structure FloatInstr where
  op : FOp
  ty : FTy
  srcTys : List FTy := []
  cmpTy : Option DType := none
  rnd : Option FloatRound := none
  mode : FMode := .ieee
  ftz : Bool := false
  sat : Bool := false
  relu : Bool := false
  oob : Bool := false
  nanMod : Bool := false
  xorsign : Bool := false
  absMod : Bool := false
  dsts : List (Option Nat)
  srcs : List Opnd
  deriving DecidableEq, Repr

namespace Decode

/-- A floating comparison operator; `lo`, `ls`, `hi` and `hs` are integer-only. -/
def FloatInstr.cmp? : Option Isa.Token → M FCmp
  | some .eq => pure (.ord .eq) | some .ne => pure (.ord .ne) | some .lt => pure (.ord .lt)
  | some .le => pure (.ord .le) | some .gt => pure (.ord .gt) | some .ge => pure (.ord .ge)
  | some .equ => pure (.unord .eq) | some .neu => pure (.unord .ne)
  | some .ltu => pure (.unord .lt) | some .leu => pure (.unord .le)
  | some .gtu => pure (.unord .gt) | some .geu => pure (.unord .ge)
  | some .num => pure .num | some .nan => pure .nan
  | _ => throw "floating comparison operator"

/-- The floating type of a type token. -/
def FloatInstr.fty (t : Option Isa.Token) : M FTy := do
  match FTy.ofDType? (← dtype t) with
  | some f => pure f
  | none => throw "floating type"

/-- The `float`-family instruction of a recognized instruction. -/
def FloatInstr.ofRaw (env : Env) (r : Isa.Raw) : M FloatInstr := do
  let mode := r.get .mode
  let rndOf : Option Isa.Token → M (Option FloatRound)
    | none => pure none
    | some .rn => pure (some .rn) | some .rz => pure (some .rz)
    | some .rm => pure (some .rm) | some .rp => pure (some .rp)
    | some _ => throw "floating rounding modifier"
  let (fmode, rnd) ← match mode with
    | some .approx => pure (FMode.approx, none)
    | some .full => pure (FMode.full, none)
    | some t@.rn | some t@.rz | some t@.rm | some t@.rp => do pure (FMode.ieee, ← rndOf (some t))
    | some _ => throw "floating mode"
    | none => do pure (FMode.ieee, ← rndOf (r.get .rnd))
  let op : FOp ← match r.entry with
    | .add | .add_half | .add_mixed_vec_up | .add_mixed_vec_down_f16
    | .add_mixed_vec_down_bf16 => pure .add
    | .sub | .sub_half | .sub_mixed_vec_up | .sub_mixed_vec_down_f16
    | .sub_mixed_vec_down_bf16 => pure .sub
    | .mul | .mul_half | .mul_mixed_vec_down_f16 | .mul_mixed_vec_down_bf16
    | .mul_mixed_vec_bf16_f16 | .mul_mixed_vec_f16_bf16 => pure .mul
    | .fma | .fma_half | .fma_mixed_vec => pure .fma
    | .mad_f => pure .mad
    | .div_f => pure .div
    | .rcp => pure .rcp
    | .sqrt => pure .sqrt
    | .rsqrt => pure .rsqrt
    | .ex2 | .ex2_half => pure .ex2
    | .lg2 => pure .lg2
    | .sin => pure .sin
    | .cos => pure .cos
    | .tanh | .tanh_half => pure .tanh
    | .abs_f | .abs_half => pure .abs
    | .neg | .neg_half => pure .neg
    | .min_f | .min3 => pure .min
    | .max_f | .max3 => pure .max
    | .copysign => pure .copysign
    | .testp => match r.get .op with
      | some .finite => pure (.testp .finite) | some .infinite => pure (.testp .infinite)
      | some .number => pure (.testp .number) | some .notanumber => pure (.testp .notanumber)
      | some .normal => pure (.testp .normal) | some .subnormal => pure (.testp .subnormal)
      | _ => throw "testp property"
    | .setp_f | .setp_pq_f | .setp_bool_f | .setp_bool_pq_f | .setp_half | .setp_half_pq
    | .setp_half_bool | .setp_half_bool_pq =>
      pure <| FOp.setp (← FloatInstr.cmp? (r.get .cmp)) (← IntInstr.boolOp? (r.get .boolop))
    | .set_f | .set_bool_f | .set_half | .set_half_bool =>
      pure <| FOp.set (← FloatInstr.cmp? (r.get .cmp)) (← IntInstr.boolOp? (r.get .boolop))
        (← dtype (r.get .dtype))
    | _ => throw "not a floating instruction"
  if flag r .relu && (op == .min || op == .max) then throw "floating min/max with .relu"
  let mixed : Bool := match r.entry with
    | .add | .sub | .fma => flag r .srctype
    | .add_mixed_vec_up | .sub_mixed_vec_up | .add_mixed_vec_down_f16
    | .sub_mixed_vec_down_f16 | .add_mixed_vec_down_bf16 | .sub_mixed_vec_down_bf16
    | .fma_mixed_vec | .mul_mixed_vec_down_f16 | .mul_mixed_vec_down_bf16
    | .mul_mixed_vec_bf16_f16 | .mul_mixed_vec_f16_bf16 => true
    | _ => false
  let (ty, cmpTy) ← match r.entry with
    | .set_f | .set_bool_f | .set_half | .set_half_bool => do
      let s ← dtype (r.get .stype)
      match FTy.ofDType? s with
      | some f => pure (f, none)
      | none => pure (← FloatInstr.fty (r.get .dtype), some s)
    | .add_mixed_vec_up | .sub_mixed_vec_up | .add_mixed_vec_down_f16
    | .sub_mixed_vec_down_f16 | .add_mixed_vec_down_bf16 | .sub_mixed_vec_down_bf16
    | .fma_mixed_vec | .mul_mixed_vec_down_f16 | .mul_mixed_vec_down_bf16
    | .mul_mixed_vec_bf16_f16 | .mul_mixed_vec_f16_bf16 => do
      pure (← FloatInstr.fty (r.get .dtype), none)
    | _ => do pure (← FloatInstr.fty (r.get .type), none)
  let srcOps := r.opnds.filter (·.role != .w)
  let srcTys ← if mixed then
      (srcOps.filter (·.dtype != some .pred)).mapM fun o => do
        match FTy.ofDType? (← ROpnd.dtype o) with
        | some f => pure f
        | none => throw "mixed-precision source type"
    else pure []
  let (dsts, srcs) ← operands env r
  if dsts.all (·.isNone) then throw "no destination register"
  return { op, ty, srcTys, cmpTy, rnd, mode := fmode, ftz := flag r .ftz, sat := flag r .sat,
           relu := flag r .relu, oob := flag r .oob, nanMod := flag r .nan,
           xorsign := flag r .xorsign, absMod := flag r .abs, dsts, srcs }

end Decode

/-- The rule of a floating instruction: THREAD-FLOAT for every form except `div.full`, whose
manual text gives no determined result, the mixed `fma` with a packed half `.atype`, whose syntax
and Semantics give its `b` operand different widths, and the `mul` forms that mix `.f16x2` and
`.bf16x2`, which convert between the two formats without a stated rounding. -/
def FloatInstr.rule (f : FloatInstr) : Option RuleId :=
  let halfPacked (t : FTy) : Bool := t.lanes == 2 && (t.fmt == .f16 || t.fmt == .bf16)
  if f.op == .div && f.mode == .full then none
  else if f.op == .fma && f.srcTys.any halfPacked then none
  else if f.op == .mul && halfPacked f.ty && f.srcTys.any halfPacked then none
  else some .threadFloat

end PTX
