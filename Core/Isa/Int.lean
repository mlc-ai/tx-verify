-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule

@[expose] public section

/-!
# Integer and bit instructions

The representation of the integer, bit, logic, comparison and selection instructions and its
construction from a recognized instruction.
-/

namespace PTX

/-! ## PROG-ISA-INT — integer and bit instructions
Statement: An integer instruction is its operation with the operation's own qualifiers, its data
  type, its saturation qualifier, its destination registers and its source operands. Every entry of
  the `int` family decodes to it; operands are resolved at the widths of their table types.

Defs: MulMode, PrmtMode, IntOp, IntInstr, Decode.IntInstr.cmp?, Decode.IntInstr.boolOp?,
  Decode.ikind, Decode.IntInstr.ofRaw, DType.intLanes?, Cmp.intOk, IntInstr.rule

Source:
- §9.7.1: "add{.sat}.type2 d, a, b;"
- §9.7.1: "mul.mode.type d, a, b;"
- §9.7.1: ".mode = { .hi, .lo, .wide };"
- §9.7.1: "mad.mode.type d, a, b, c;"
- §9.7.1: "min{.relu}.type2 d, a, b;"
- §9.7.7.2: "setp.CmpOp{.ftz}.type p[|q], a, b;"
- §9.7.7.2: "setp.CmpOp.BoolOp{.ftz}.type p[|q], a, b, {!}c;"
- §9.7.7.3: "selp.type d, a, b, c;"
- §9.7.9: "and.type d, a, b;"
- §9.7.9: "shl.type d, a, b;"
- §9.7.9: "shr.type d, a, b;"
- §9.7.9: "lop3.b32 d, a, b, c, immLut;"
- §9.7.9: "shf.l.mode.b32 d, a, b, c;"
- §9.7.1.5: "clmad.mode.u64 d, a, b, c;"
- §9.7.1.24: "dp4a.atype.btype d, a, b, c;"
- §9.7.1.25: "dp2a.mode.atype.btype d, a, b, c;"
- §9.7.2: "add.cc.type d, a, b;"
- §9.7.2: "addc{.cc}.type d, a, b;"
- §9.7.2: "sub.cc.type d, a, b;"
- §9.7.2: "subc{.cc}.type d, a, b;"
- §9.7.2: "mad{.hi,.lo}.cc.type d, a, b, c;"
- §9.7.2: "madc{.hi,.lo}{.cc}.type d, a, b, c;"
- §9.7.2: ".type = { .u32, .s32, .u64, .s64 };"
- §9.7.9.6: "immLut is an integer constant that can take values from 0 to 255"
- §9.7.10.7: "prmt.b32{.mode} d, a, b, c;"
- §9.7.7.1: "The signed and unsigned comparison operators are eq , ne , lt , le , gt , ge . For
    unsigned values, the comparison operators lo , ls , hi , and hs for lower, lower-or-same,
    higher, and higher-or-same may be used instead of lt , le , gt , ge , respectively. The untyped,
    bit-size comparisons are eq and ne ."

Direction: representation

Applies: Every instruction of the `int` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `IntInstr.rule` selects THREAD-INT for the integer forms of the manual's
  syntax, THREAD-MOVE for `selp` and `slct`, and no rule for combinations outside the syntax. The
  model does not decode a negated predicate source `!c`, an `immLut` outside 0 to 255 is rejected,
  and so is a `setp` whose `p` and `q` are both the sink (§9.7.7.2: "The sink symbol ‘_’ may be used
  in place of any one of the destination operands."). `slct.ftz` keeps `.ftz` in `IntOp.slct`.
  `IntInstr.rule` checks each operation's types, qualifiers and destinations against its syntax:
  `.sat` only where the manual allows it, `.relu` only on the signed types it lists, comparison
  operators by `Cmp.intOk`, one destination except the `p|q` pair of `setp` (two distinct registers,
  or one register and the sink) and the `d|p` pair of `lop3.BoolOp`. The extended-precision
  instructions of §9.7.2 are their own entries of the grammar (`Tools/isa/extra.py`), since the TIRx
  table has none of them. They decode to `IntOp.addCarry`, `IntOp.subCarry` and `IntOp.madCarry`,
  which record whether the instruction reads the carry flag (`addc`, `subc`, `madc`) and whether it
  writes it (`.cc`). The grammar requires the `.hi` or `.lo` mode of `mad.cc` and `madc`, because
  their Semantics sections define only these two variants, so a form without a mode is not
  recognized.
-/

/-- The `.mode` of `mul` and `mad`. -/
inductive MulMode where
  | lo | hi | wide
  deriving DecidableEq, Repr

/-- The `.mode` of `prmt`. -/
inductive PrmtMode where
  | f4e | b4e | rc8 | ecl | ecr | rc16
  deriving DecidableEq, Repr

/-- An integer, bit, logic, comparison or selection operation with its own qualifiers. -/
inductive IntOp where
  | add | sub
  /-- `add.cc` (`cin` false) and `addc{.cc}` (`cin` true); `cout` is `.cc` (§9.7.2). -/
  | addCarry (cin cout : Bool)
  /-- `sub.cc` (`cin` false) and `subc{.cc}` (`cin` true); `cout` is `.cc` (§9.7.2). -/
  | subCarry (cin cout : Bool)
  /-- `mad{.hi,.lo}.cc` (`cin` false) and `madc{.hi,.lo}{.cc}` (`cin` true) (§9.7.2). -/
  | madCarry (hi cin cout : Bool)
  | mul (m : MulMode)
  | mad (m : MulMode)
  | mul24 (hi : Bool)
  | mad24 (hi : Bool)
  | clmad (hi : Bool)
  | sad | div | rem | abs | neg
  | min (relu : Bool)
  | max (relu : Bool)
  | popc | clz
  | bfind (shiftamt : Bool)
  | fns | brev | bfe | bfi
  | szext (clamp : Bool)
  | bmsk (clamp : Bool)
  | dp4a (aty bty : IType)
  | dp2a (hi : Bool) (aty bty : IType)
  | and | or | xor | not | cnot
  | lop3 (lut : Int) (bop : Option BoolOp)
  | shf (left clamp : Bool)
  | shl | shr
  | prmt (mode : Option PrmtMode)
  | selp
  | slct (ctype : DType) (ftz : Bool)
  | setp (c : Cmp) (bop : Option BoolOp)
  | set (c : Cmp) (bop : Option BoolOp) (dst : DType)
  deriving DecidableEq, Repr

/-- An integer instruction: the operation, the data type (`.type`, or the source type of `set`
and `slct`), `.sat`, the destinations (`none` for the sink `_`) and the sources in operand
order. -/
structure IntInstr where
  op : IntOp
  ty : DType
  sat : Bool := false
  dsts : List (Option Nat)
  srcs : List Opnd
  deriving DecidableEq, Repr

namespace Decode

/-- An integer comparison operator. -/
def IntInstr.cmp? : Option Isa.Token → M Cmp
  | some .eq => pure .eq | some .ne => pure .ne | some .lt => pure .lt
  | some .le => pure .le | some .gt => pure .gt | some .ge => pure .ge
  | some .lo => pure .lo | some .ls => pure .ls | some .hi => pure .hi
  | some .hs => pure .hs
  | _ => throw "integer comparison operator"

/-- The `.BoolOp` of a comparison. -/
def IntInstr.boolOp? : Option Isa.Token → M (Option BoolOp)
  | none => pure none
  | some .and => pure (some .and)
  | some .or => pure (some .or)
  | some .xor => pure (some .xor)
  | some _ => throw "boolean operator"

/-- The integer kind of an `.atype`/`.btype` token. -/
def ikind : Option Isa.Token → M IType
  | some .u32 => pure .u
  | some .s32 => pure .s
  | _ => throw "dp4a/dp2a operand type"

/-- The `int`-family instruction of a recognized instruction. -/
def IntInstr.ofRaw (env : Env) (r : Isa.Raw) : M IntInstr := do
  let hi := r.get .mode == some .hi
  let clamp := r.get .mode == some .clamp
  if (flag r .ftz && r.entry != .slct) || flag r .nan || flag r .xorsign || flag r .abs then
    throw "floating qualifier on an integer instruction"
  let op : IntOp ← match r.entry with
    | .add_int => pure .add
    | .sub_int => pure .sub
    | .add_cc => pure (.addCarry false true)
    | .addc => pure (.addCarry true (flag r .cc))
    | .sub_cc => pure (.subCarry false true)
    | .subc => pure (.subCarry true (flag r .cc))
    | .mad_cc => pure (.madCarry hi false true)
    | .madc => pure (.madCarry hi true (flag r .cc))
    | .mul_int => pure (.mul (if hi then .hi else .lo))
    | .mul_wide => pure (.mul .wide)
    | .mad_int => pure (.mad (if hi then .hi else .lo))
    | .mad_wide => pure (.mad .wide)
    | .mul24 => pure (.mul24 hi)
    | .mad24 => pure (.mad24 hi)
    | .clmad => pure (.clmad hi)
    | .sad => pure .sad
    | .div => pure .div
    | .rem => pure .rem
    | .abs => pure .abs
    | .neg_int => pure .neg
    | .min_int => pure (.min (flag r .relu))
    | .max_int => pure (.max (flag r .relu))
    | .popc => pure .popc
    | .clz => pure .clz
    | .bfind => pure (.bfind (flag r .shiftamt))
    | .fns => pure .fns
    | .brev => pure .brev
    | .bfe => pure .bfe
    | .bfi => pure .bfi
    | .szext => pure (.szext clamp)
    | .bmsk => pure (.bmsk clamp)
    | .dp4a => pure <| IntOp.dp4a (← ikind (r.get .atype)) (← ikind (r.get .btype))
    | .dp2a => pure <| IntOp.dp2a hi (← ikind (r.get .atype)) (← ikind (r.get .btype))
    | .and => pure .and
    | .or => pure .or
    | .xor => pure .xor
    | .not => pure .not
    | .cnot => pure .cnot
    | .lop3 | .lop3_bool | .lop3_bool_sink => do
      let .literal t ← arg r "immLut" | throw "lop3 immLut"
      let .imm lut ← literal t | throw "lop3 immLut"
      unless 0 ≤ lut ∧ lut < 256 do throw "lop3 immLut out of range"
      pure <| IntOp.lop3 lut (← IntInstr.boolOp? (r.get .boolop))
    | .shf => pure (.shf (r.get .dir == some .l) clamp)
    | .shl => pure .shl
    | .shr => pure .shr
    | .prmt => pure (.prmt (match r.get .mode with
        | some .f4e => some .f4e | some .b4e => some .b4e | some .rc8 => some .rc8
        | some .ecl => some .ecl | some .ecr => some .ecr | some .rc16 => some .rc16
        | _ => none))
    | .selp => pure .selp
    | .slct => pure <| IntOp.slct (← dtype (r.get .ctype)) (flag r .ftz)
    | .setp_int | .setp_pq_int | .setp_bool_int | .setp_bool_pq_int =>
      pure <| IntOp.setp (← IntInstr.cmp? (r.get .cmp)) (← IntInstr.boolOp? (r.get .boolop))
    | .set_int | .set_bool_int =>
      pure <| IntOp.set (← IntInstr.cmp? (r.get .cmp)) (← IntInstr.boolOp? (r.get .boolop))
        (← dtype (r.get .dtype))
    | .set_packed => pure <| IntOp.set (← IntInstr.cmp? (r.get .cmp)) none (.int .b 32)
    | _ => throw "not an integer instruction"
  let ty ← match r.entry with
    | .set_int | .set_bool_int => dtype (r.get .stype)
    | .slct => dtype (r.get .dtype)
    | .dp4a | .dp2a => pure (.int .b 32)
    | _ => dtype (r.get .type)
  let ops := r.opnds.filter (·.kind != .imm)
  let (dsts, srcs) ← operands env { r with opnds := ops }
  let dsts := match r.entry with
    | .lop3_bool_sink => none :: dsts
    | _ => dsts
  if dsts.all (·.isNone) then throw "no destination register"
  return { op, ty, sat := flag r .sat, dsts, srcs }

end Decode

/-- The integer kind, lane width and lane count of an integer type (one lane) or of a packed
type of integer lanes (`.u16x2` is `(.u, 16, 2)`). -/
def DType.intLanes? : DType → Option (IType × Nat × Nat)
  | .int k w => some (k, w, 1)
  | .packed (.int k w) n => some (k, w, n)
  | _ => none

/-- Whether a comparison operator applies to integers of kind `k` (§9.7.7.2): `eq` and `ne` to
every kind, `lt` to `ge` to the signed and unsigned kinds, `lo` to `hs` to the unsigned kind. -/
def Cmp.intOk (c : Cmp) (k : IType) : Bool :=
  [Cmp.eq, .ne].contains c || (k != .b && [Cmp.lt, .le, .gt, .ge].contains c) ||
    (k == .u && [Cmp.lo, .ls, .hi, .hs].contains c)

/-- The rule of an integer instruction: THREAD-INT for the integer forms of the manual's syntax,
THREAD-MOVE for `selp` and `slct`, and none for any qualifier, type or destination combination
outside the syntax. -/
def IntInstr.rule (i : IntInstr) : Option RuleId :=
  let one := match i.dsts with | [some _] => true | _ => false
  -- `p|q` of `setp`: at least one register, and two distinct registers
  let pair := match i.dsts with
    | [some p, some q] => p != q
    | [some _, none] | [none, some _] => true
    | _ => false
  let is (ks : List IType) (ws : List Nat) : Bool := match i.ty with
    | .int k w => ks.contains k && ws.contains w
    | _ => false
  let us := is [.u, .s] [16, 32, 64]
  let x2 (ks : List IType) : Bool := ks.any fun k => i.ty == .packed (.int k 16) 2
  let x4 (ks : List IType) : Bool := ks.any fun k => i.ty == .packed (.int k 8) 4
  let plain := !i.sat
  let cmpOk (c : Cmp) : Bool := match i.ty.intLanes? with
    | some (k, _, _) => c.intOk k
    | none => false
  let ok : Bool := match i.op with
    | .add => one && (us || x2 [.u, .s] || x4 [.u, .s]) &&
        (plain || is [.u, .s] [32] || x2 [.u, .s] || x4 [.u, .s])
    | .sub => one && (us || x4 [.u, .s]) && (plain || is [.s] [32] || x4 [.u, .s])
    | .mul .lo | .mul .hi | .mad .lo | .sad | .div | .rem => one && plain && us
    | .mad .hi => one && us && (plain || is [.s] [32])
    | .mul .wide | .mad .wide => one && plain && is [.u, .s] [16, 32]
    | .addCarry _ _ | .subCarry _ _ | .madCarry _ _ _ => one && plain && is [.u, .s] [32, 64]
    | .mul24 _ => one && plain && is [.u, .s] [32]
    | .mad24 hi => one && is [.u, .s] [32] && (plain || (hi && is [.s] [32]))
    | .abs | .neg => one && plain && is [.s] [16, 32, 64]
    | .min relu | .max relu => one && plain && (us || x2 [.u, .s] || x4 [.u, .s]) &&
        (!relu || is [.s] [32] || x2 [.s] || x4 [.s])
    | .clmad _ => one && plain && is [.u] [64]
    | .dp4a _ _ | .dp2a _ _ _ => one && plain && is [.b] [32]
    | .popc | .clz | .brev => one && plain && is [.b] [32, 64]
    | .bfind _ | .bfe => one && plain && is [.u, .s] [32, 64]
    | .bfi => one && plain && is [.b] [32, 64]
    | .fns | .bmsk _ | .prmt _ | .shf _ _ => one && plain && is [.b] [32]
    | .szext _ => one && plain && is [.u, .s] [32]
    | .and | .or | .xor | .not => one && plain && (i.ty == .pred || is [.b] [16, 32, 64])
    | .cnot | .shl => one && plain && is [.b] [16, 32, 64]
    | .shr => one && plain && is [.b, .u, .s] [16, 32, 64]
    | .lop3 lut bop => plain && is [.b] [32] && 0 ≤ lut && lut < 256 &&
        match bop, i.dsts with
        | none, [some _] => true
        | some _, [_, some _] => true
        | _, _ => false
    | .setp c _ => (one || pair) && plain && is [.b, .u, .s] [16, 32, 64] && cmpOk c
    | .set c bop dst => one && plain && cmpOk c &&
        ((is [.b, .u, .s] [16, 32, 64] &&
            [DType.int .u 32, .int .s 32, .float .f32].contains dst) ||
          ((x2 [.u, .s] || x4 [.u, .s]) && bop == none && dst == .int .b 32))
    | _ => false
  match i.op with
  | .selp => if one && plain then some .threadMove else none
  | .slct ct ftz =>
    if one && plain && (ct == .float .f32 || (ct == .int .s 32 && !ftz)) then some .threadMove
    else none
  | _ => if ok then some .threadInt else none

end PTX
