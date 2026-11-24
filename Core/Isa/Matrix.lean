-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Isa.Mem

@[expose] public section

/-!
# Warp-level matrix instructions

`ldmatrix`, `stmatrix`, `movmatrix`, `mma` and `mma.sp` (`MatrixInstr`).
-/

namespace PTX

/-! ## PROG-ISA-MATRIX — warp-level matrix instructions
Statement: A warp-level matrix instruction is its operation with the operation's qualifiers, its
  state space and address for `ldmatrix` and `stmatrix`, its destination registers and its source
  registers. Every `ldmatrix`, `stmatrix`, `movmatrix`, `mma` and `mma.sp` entry of the `matrix`
  family decodes to it. `spcompress` and `spdecompress` have no representation.

Defs: MatrixShape, MatrixFmt, MatrixMove, MatrixMove.rows, MatrixMove.regsPerMatrix,
  MatrixMove.supported, MmaTypes, MmaBitOp, MmaSpec, MmaSpec.quad, MmaSpec.kc, MmaSpec.regBits,
  MmaSpec.elems, MmaSpec.regs, MmaSpec.supported, MatrixOp, MatrixInstr,
  Decode.MatrixInstr.mmaShape?, Decode.MatrixInstr.moveShape?, Decode.MatrixInstr.num?,
  Decode.MatrixInstr.srcsOf, Decode.MatrixInstr.dstsOf, Decode.MatrixInstr.ofRaw,
  MatrixInstr.rule

Source:
- §9.7.16.5.15: "ldmatrix.sync.aligned.shape.num{.trans}{.ss}.type r, [p];
    ldmatrix.sync.aligned.m8n16.num{.ss}.dst_fmt.src_fmt r, [p];
    ldmatrix.sync.aligned.m16n16.num.trans{.ss}.dst_fmt.src_fmt r, [p];
    ldmatrix.sync.aligned.m8n16.num{.ss}.dtype.ctype r, [p];"
- §9.7.16.5.15: "When .shape is .m16n16 , only .x1 and .x2 are valid values for .num ."
- §9.7.16.5.15: "However, for 16x16 matrices, .trans is mandatory."
- §9.7.16.5.16: "stmatrix.sync.aligned.shape.num{.trans}{.ss}.type [p], r;"
- §9.7.16.5.16: ".m16n8 shape is valid only for .b8 type."
- §9.7.16.5.16: "However, for 16x8 matrices, .trans is mandatory."
- §9.7.16.5.17: "movmatrix.sync.aligned.shape.trans.type d, a;"
- §9.7.16.5.14: "mma.sync.aligned.m8n8k4.alayout.blayout.dtype.f16.f16.ctype d, a, b, c;"
- §9.7.16.5.14: "Single bit: mma.sync.aligned.shape.row.col.s32.b1.b1.s32.bitOp.popc d, a, b, c;"
- §9.7.16.6.3: "mma.spvariant.sync.aligned.m16n8k16.row.col.dtype.f16.f16.ctype d, a, b, c, e, f;"
- §9.7.16.6.3: "Operand e is a 32-bit integer and operand f is a 32-bit integer constant with values
    in the range 0..3."

Direction: representation

Applies: Every instruction of the `matrix` family

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `MatrixInstr.rule` selects THREAD-MATRIX for the `ldmatrix`, `stmatrix`
  and `movmatrix` forms the manual's syntax lines give and THREAD-MMA-SYNC for `mma` and `mma.sp`.
  A matrix move (`MatrixMove`) records whether it stores, its shape, the number of matrices,
  `.trans` and the element format: `.b16`, `.b8`, the expanded `.b8x16` with its packed source
  format, or `.s8.s4`. An MMA (`MmaSpec`) records its shape, the layouts of A and B, the element
  types of A, B, C and D with the rounding modifier of `.f64`, `.satfinite`, the single-bit
  operation and, for `mma.sp`, whether the metadata is ordered and the sparsity selector `f`. The
  destination and source registers are listed in operand order: an MMA's sources are A, B and C
  followed by the metadata `e`.
  `MatrixInstr.rule` gives a rule only to the forms of the manual's syntax lines, which are narrower
  than the table: `ldmatrix` of `.b16` at `.m8n8`, of `.b8` at `.m16n16` with `.trans`, of `.b8x16`
  at `.m8n16` without `.trans` and at `.m16n16` with `.trans`; `stmatrix` of `.b16` at `.m8n8` and
  of `.b8` at `.m16n8` with `.trans`; `movmatrix`; and every `mma` and `mma.sp` shape and type of
  the table (`MmaSpec.supported`), each with the register counts of its fragments (`MmaSpec.regs`).
  `ldmatrix.m8n16.s8.s4` has no rule: the text gives neither the number of bytes of a source row nor
  the order of the 4-bit elements in it.
-/

/-- The shape of an `ldmatrix` or `stmatrix` matrix. -/
inductive MatrixShape where
  | m8n8 | m16n16 | m8n16 | m16n8
  deriving DecidableEq, Repr

/-- The element format of an `ldmatrix` or `stmatrix`: `.b16`, `.b8`, `.b8x16` expanded from
`.b6x16_p32` (`six`) or `.b4x16_p64`, or `.s8.s4`. -/
inductive MatrixFmt where
  | b16
  | b8
  | b8x16 (six : Bool)
  | s8s4
  deriving DecidableEq, Repr

/-- An `ldmatrix` (`store` false) or `stmatrix` (`store` true): shape, number of matrices (1, 2
or 4), `.trans` and element format. -/
structure MatrixMove where
  store : Bool
  shape : MatrixShape
  num : Nat
  trans : Bool
  fmt : MatrixFmt
  deriving DecidableEq, Repr

/-- The memory rows of one matrix, each supplied by one thread: 16 for `.m16n16`, 8 otherwise. -/
def MatrixMove.rows (m : MatrixMove) : Nat :=
  match m.shape with
  | .m16n16 => 16
  | _ => 8

/-- The 32-bit registers of one matrix in each thread: 2 for `.m16n16`, 1 otherwise. -/
def MatrixMove.regsPerMatrix (m : MatrixMove) : Nat :=
  match m.shape with
  | .m16n16 => 2
  | _ => 1

/-- The forms of the manual's syntax lines: `ldmatrix` `.m8n8.b16`, `.m16n16.trans.b8`,
`.m8n16.b8x16` and `.m16n16.trans.b8x16`; `stmatrix` `.m8n8.b16` and `.m16n8.trans.b8`; `.num` is
`.x1`, `.x2` or `.x4`, and only `.x1` or `.x2` at `.m16n16`. -/
def MatrixMove.supported (m : MatrixMove) : Bool :=
  (m.num == 1 || m.num == 2 || (m.num == 4 && m.shape != .m16n16)) &&
  match m.store, m.shape, m.trans, m.fmt with
  | false, .m8n8, _, .b16 | false, .m16n16, true, .b8 | false, .m8n16, false, .b8x16 _
  | false, .m16n16, true, .b8x16 _ | true, .m8n8, _, .b16 | true, .m16n8, true, .b8 => true
  | _, _, _, _ => false

/-- The element types of a warp-level MMA: A, B, C and D, with the rounding modifier of `.f64`
(`none` when it is not written). -/
structure MmaTypes where
  a : DType
  b : DType
  c : DType
  d : DType
  rnd : Option FloatRound := none
  deriving DecidableEq, Repr

/-- The logical operation of a single-bit MMA. -/
inductive MmaBitOp where
  | xor | and
  deriving DecidableEq, Repr

/-- An `mma` or `mma.sp`: the shape `m × n × k`, whether A is row-major and B column-major, the
element types, `.satfinite`, the single-bit operation and, for `mma.sp`, whether the metadata is
ordered (`.sp::ordered_metadata`) and the sparsity selector. -/
structure MmaSpec where
  m : Nat
  n : Nat
  k : Nat
  aRow : Bool := true
  bCol : Bool := true
  types : MmaTypes
  satfinite : Bool := false
  bitOp : Option MmaBitOp := none
  sparse : Option (Bool × Nat) := none
  deriving DecidableEq, Repr

/-- `mma.m8n8k4` with `.f16` A and B, which computes four MMAs per warp (§9.7.16.5.1). -/
def MmaSpec.quad (s : MmaSpec) : Bool :=
  s.m == 8 && s.n == 8 && s.k == 4 && s.types.a == .float .f16

/-- The columns of the A operand the threads hold: `k / 2` for `mma.sp`, `k` otherwise. -/
def MmaSpec.kc (s : MmaSpec) : Nat := if s.sparse.isSome then s.k / 2 else s.k

/-- The width of one register of an operand of element type `t`: 64 bits for `.f64`, 32
otherwise. -/
def MmaSpec.regBits (t : DType) : Nat := if t == .float .f64 then 64 else 32

/-- The elements of A, B, C and D each thread holds: 4, 4, 8 and 8 for the four-MMA form, and
otherwise `m × kc`, `k × n` and `m × n` divided by the 32 threads. -/
def MmaSpec.elems (s : MmaSpec) : Nat × Nat × Nat × Nat :=
  if s.quad then (4, 4, 8, 8)
  else (s.m * s.kc / 32, s.k * s.n / 32, s.m * s.n / 32, s.m * s.n / 32)

/-- The registers of A, B, C and D each thread holds: its elements times the element width,
divided by the register width. -/
def MmaSpec.regs (s : MmaSpec) : Nat × Nat × Nat × Nat :=
  let (ea, eb, ec, ed) := s.elems
  let r (e : Nat) (t : DType) := e * t.width / MmaSpec.regBits t
  (r ea s.types.a, r eb s.types.b, r ec s.types.c, r ed s.types.d)

/-- The shapes and types of the manual's `mma` and `mma.sp` syntax lines (§9.7.16.5.14,
§9.7.16.6.3) whose fragments the manual gives: A and B of one width class, the accumulator types
of that class, and a shape of the class. -/
def MmaSpec.supported (s : MmaSpec) : Bool :=
  let t := s.types
  let f16like (x : DType) := x == .float .f16 || x == .float .bf16
  let f8 (x : DType) := x == .float .e4m3 || x == .float .e5m2
  let i8 (x : DType) := x == .int .u 8 || x == .int .s 8
  let i4 (x : DType) := x == .int .u 4 || x == .int .s 4
  let facc := (t.c == .float .f16 || t.c == .float .f32) &&
    (t.d == .float .f16 || t.d == .float .f32)
  let f32acc := t.c == .float .f32 && t.d == .float .f32
  let iacc := t.c == .int .s 32 && t.d == .int .s 32
  let shape (m k : Nat) := s.m == m && s.n == 8 && s.k == k
  let dense := s.sparse.isNone
  let noBits := s.bitOp.isNone && !s.satfinite
  let noRnd := t.rnd.isNone
  (s.sparse.all fun (_, sel) => decide (sel < 4)) && (dense || (s.aRow && s.bCol)) &&
  if f16like t.a && t.b == t.a then
    facc && noBits && noRnd &&
      (if dense then (t.a == .float .f16 && shape 8 4) || shape 16 8 || shape 16 16
       else shape 16 16 || shape 16 32) &&
      (t.a == .float .f16 || f32acc) && (s.quad || (s.aRow && s.bCol))
  else if t.a == .float .tf32 && t.b == t.a then
    f32acc && noBits && noRnd && s.aRow && s.bCol &&
      (if dense then shape 16 4 || shape 16 8 else shape 16 8 || shape 16 16)
  else if t.a == .float .f64 && t.b == t.a then
    t.c == t.a && t.d == t.a && noBits && dense && s.aRow && s.bCol &&
      (shape 8 4 || shape 16 4 || shape 16 8 || shape 16 16)
  else if f8 t.a && f8 t.b then
    facc && noBits && noRnd && s.aRow && s.bCol &&
      (if dense then shape 16 16 || shape 16 32 else shape 16 64 && f32acc)
  else if i8 t.a && i8 t.b then
    iacc && s.bitOp.isNone && noRnd && s.aRow && s.bCol &&
      (if dense then shape 8 16 || shape 16 16 || shape 16 32 else shape 16 32 || shape 16 64)
  else if i4 t.a && i4 t.b then
    iacc && s.bitOp.isNone && noRnd && s.aRow && s.bCol &&
      (if dense then shape 8 32 || shape 16 32 || shape 16 64
       else shape 16 64 || shape 16 128)
  else if t.a == .int .b 1 && t.b == t.a then
    iacc && s.bitOp.isSome && !s.satfinite && noRnd && dense && s.aRow && s.bCol &&
      (shape 8 128 || shape 16 128 || shape 16 256)
  else false

/-- The operation of a warp-level matrix instruction: a matrix load or store, the transpose
`movmatrix.sync.aligned.m8n8.trans.b16`, or an MMA. -/
inductive MatrixOp where
  | move (m : MatrixMove)
  | transpose
  | mma (s : MmaSpec)
  deriving DecidableEq, Repr

/-- A warp-level matrix instruction: its operation, the state space (`none` for a generic
address) and address of a matrix load or store, its destination registers and its source
registers (an MMA's A, B and C, then its metadata). -/
structure MatrixInstr where
  op : MatrixOp
  space : Option StateSpace := none
  addr : Option Addr := none
  dsts : List Nat := []
  srcs : List Opnd := []
  deriving DecidableEq, Repr

namespace Decode
open PTX.Syntax

/-- The shape `(m, n, k)` of an `mma` shape token. -/
def MatrixInstr.mmaShape? : Option Isa.Token → Option (Nat × Nat × Nat)
  | some .m8n8k4 => some (8, 8, 4)
  | some .m8n8k16 => some (8, 8, 16)
  | some .m8n8k32 => some (8, 8, 32)
  | some .m8n8k128 => some (8, 8, 128)
  | some .m16n8k4 => some (16, 8, 4)
  | some .m16n8k8 => some (16, 8, 8)
  | some .m16n8k16 => some (16, 8, 16)
  | some .m16n8k32 => some (16, 8, 32)
  | some .m16n8k64 => some (16, 8, 64)
  | some .m16n8k128 => some (16, 8, 128)
  | some .m16n8k256 => some (16, 8, 256)
  | _ => none

/-- The shape of an `ldmatrix` or `stmatrix` shape token. -/
def MatrixInstr.moveShape? : Option Isa.Token → Option MatrixShape
  | some .m8n8 => some .m8n8
  | some .m16n16 => some .m16n16
  | some .m8n16 => some .m8n16
  | some .m16n8 => some .m16n8
  | _ => none

/-- The number of matrices of a `.num` token. -/
def MatrixInstr.num? : Option Isa.Token → Option Nat
  | some .x1 => some 1
  | some .x2 => some 2
  | some .x4 => some 4
  | _ => none

/-- The source registers of a recognized operand, or none when it is absent. -/
def MatrixInstr.srcsOf (env : Env) (r : Isa.Raw) (name : String) : M (List Opnd) :=
  match opnd? r name with
  | some o => rsrcs env o
  | none => pure []

/-- The destination registers of a recognized operand; a sink is an error. -/
def MatrixInstr.dstsOf (env : Env) (r : Isa.Raw) (name : String) : M (List Nat) := do
  let some o := opnd? r name | throw s!"missing operand {name}"
  (← rdsts env o).mapM fun d => match d with
    | some d => pure d
    | none => throw "sink destination of a matrix instruction"

/-- The warp-level matrix instruction of a recognized instruction; `none` for `spcompress` and
`spdecompress`, which have no representation. -/
def MatrixInstr.ofRaw (env : Env) (r : Isa.Raw) : M (Option MatrixInstr) := do
  match r.entry with
  | .ldmatrix | .ldmatrix_m16n16_b8 | .ldmatrix_b8fmt | .ldmatrix_s8_s4 | .stmatrix
  | .stmatrix_m16n8_b8 =>
    let store := r.entry == .stmatrix || r.entry == .stmatrix_m16n8_b8
    let some shape := MatrixInstr.moveShape? (r.get .shape) | throw "matrix shape"
    let some num := MatrixInstr.num? (r.get .num) | throw "matrix count"
    let fmt : MatrixFmt := match r.entry with
      | .ldmatrix_m16n16_b8 | .stmatrix_m16n8_b8 => .b8
      | .ldmatrix_b8fmt => .b8x16 (r.get .src_fmt == some .b6x16_p32)
      | .ldmatrix_s8_s4 => .s8s4
      | _ => .b16
    let space ← match r.get .space with
      | none => pure none
      | some t => match MemAccess.space? t with
        | some s => pure (some s)
        | none => throw "matrix state space"
    let addr ← MemAccess.addrOf env (← arg r "p")
    let move : MatrixMove := { store, shape, num, trans := flag r .trans, fmt }
    if store then
      return some { op := .move move, space, addr := some addr,
                    srcs := ← MatrixInstr.srcsOf env r "r" }
    else
      return some { op := .move move, space, addr := some addr,
                    dsts := ← MatrixInstr.dstsOf env r "r" }
  | .movmatrix =>
    return some { op := .transpose, dsts := ← MatrixInstr.dstsOf env r "d",
                  srcs := ← MatrixInstr.srcsOf env r "a" }
  | .mma | .mma_f16acc | .mma_f16c_f32d | .mma_int | .mma_f64 | .mma_sp_f16acc
  | .mma_sp_f16acc_pair | .mma_sp_int_pair | .mma_sp_int_all | .mma_sp | .mma_sp_pair
  | .mma_sp_all =>
    let some (m, n, k) := MatrixInstr.mmaShape? (r.get .shape) | throw "mma shape"
    let rnd : Option FloatRound := match r.get .rnd with
      | some .rn => some .rn | some .rz => some .rz | some .rm => some .rm
      | some .rp => some .rp | _ => none
    let types : MmaTypes := { a := ← dtype (r.get .atype), b := ← dtype (r.get .btype),
                              c := ← dtype (r.get .ctype), d := ← dtype (r.get .dtype), rnd }
    let bitOp : Option MmaBitOp := match r.get .bitop with
      | some .xor => some .xor | some .and => some .and | _ => none
    let sparse ← match r.get .spvariant with
      | none => pure none
      | some v => do
        let .literal t ← arg r "f" | throw "sparsity selector"
        let some sel := natLit? t.toList | throw "sparsity selector"
        pure (some (v == .sp_ordered_metadata, sel))
    let spec : MmaSpec := { m, n, k, aRow := r.get .alayout != some .col,
                            bCol := r.get .blayout != some .row, types,
                            satfinite := flag r .satfinite, bitOp, sparse }
    let srcs := (← MatrixInstr.srcsOf env r "a") ++ (← MatrixInstr.srcsOf env r "b") ++
      (← MatrixInstr.srcsOf env r "c") ++ (← MatrixInstr.srcsOf env r "e")
    return some { op := .mma spec, dsts := ← MatrixInstr.dstsOf env r "d", srcs }
  | _ => return none

end Decode

/-- The rule of a warp-level matrix instruction: THREAD-MATRIX for a supported matrix load or
store (`MatrixMove.supported`) with an address, a `.shared` or generic state space and one 32-bit
register per register of its matrices, and for `movmatrix`; THREAD-MMA-SYNC for a supported MMA
(`MmaSpec.supported`) with the register counts of its fragments and, for `mma.sp`, one metadata
register. -/
def MatrixInstr.rule (i : MatrixInstr) : Option RuleId :=
  match i.op with
  | .move m =>
    let n := m.num * m.regsPerMatrix
    let regsOk := if m.store then i.dsts == [] && i.srcs.length == n
      else i.srcs == [] && i.dsts.length == n
    let spaceOk := i.space == none || i.space == some (.shared .cta)
    if m.supported && regsOk && spaceOk && i.addr.isSome then some .threadMatrix else none
  | .transpose =>
    match i.dsts, i.srcs with
    | [_], [_] => some .threadMatrix
    | _, _ => none
  | .mma s =>
    let (ra, rb, rc, rd) := s.regs
    if s.supported && i.dsts.length == rd &&
        i.srcs.length == ra + rb + rc + (if s.sparse.isSome then 1 else 0) then
      some .threadMma
    else none

end PTX
