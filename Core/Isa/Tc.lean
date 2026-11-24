-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Operand
public import Core.Isa.Rule

@[expose] public section

/-!
# tcgen05 matrix multiply

The representation of every `tcgen05.mma` form of the instruction table, built from the table's
qualifier slots and operands, and the rule that selects the forms with Core semantics.
-/

namespace PTX

/-! ## PROG-ISA-TC-MMA — tcgen05.mma forms
Statement: A `tcgen05.mma` instruction is one value of `TcMmaInstr`: its CTA group, `.ws`, `.sp`,
  `.kind`, the D address, A in shared memory (a descriptor) or in Tensor Memory (an address), the B
  descriptor, the instruction descriptor, the disable-output-lane mask, `enable-input-d`, the
  zero-column mask, the collector usage of A and B, `.ashift`, the sparsity metadata address, the
  block-scale qualifier with the scale factor addresses, and the lookup-table address of
  `.decompress::lut::b`. Every `tcgen05.mma` entry of the `tc` family decodes to it.

Defs: CtaGroup, CtaGroup.size, MmaKind, MmaCollector, MmaCollector.reuses, TcMmaA, MmaScaleVec,
  MmaBlockScale, TcMmaInstr, TcMmaInstr.dense, Decode.ctaGroup?, Decode.mmaKind?,
  Decode.mmaCollectorA?, Decode.mmaCollectorB?, Decode.mmaScaleVec?, Decode.tmemDst,
  Decode.enableInput, Decode.TcMmaInstr.ofRaw, TcMmaInstr.rule

Source:
- §9.7.18.10.10.1: "tcgen05.mma.cta_group.kind [d-tmem], a-desc, b-desc, idesc, {
    disable-output-lane }, enable-input-d {, scale-input-d};"
- §9.7.18.10.10.1: "If no .collector_a_usage qualifier is specified, then it defaults to
    .collector::a::discard ."
- §9.7.18.10.10.1: "If no .collector_b_usage qualifier is specified, then it defaults to
    .collector::b::discard ."
- §9.7.18.10.10.1: "The size of the vector is as follows: .cta_group Size of the vector
    disable-output-lane ::1 4 ::2 8"
- §9.7.18.10.10.2 (tcgen05.mma.sp)
- §9.7.18.10.10.3: "tcgen05.mma.ws.cta_group::1.kind{.collector_usage} [d-tmem], a-desc, b-desc,
    idesc, enable-input-d {, zero-column-mask-desc };"
- §9.7.18.10.10.3: "If no .collector_usage qualifier is specified, then it defaults to
    .collector::b0::discard ."
- §9.7.18.10.10.4 (tcgen05.mma.ws.sp)
- §4.5.3: "In PTX, integer constants may be used as predicates."

Direction: representation

Applies: Every `tcgen05.mma` entry of the instruction table

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at the
  widths of the operand types.

Effect: Representation; `TcMmaInstr.rule` selects THREAD-TC for the forms with Core semantics.
  The D address and the Tensor Memory operands of the scale factors, the sparsity metadata and the
  lookup table are `[r]` or `[r+imm]`; the D address takes a register, written `[r]` or `[r+0]`
  (the zero offset is no offset), and the A address in Tensor Memory may carry a constant offset
  (THREAD-TC). Without the disable-output-lane operand
  (the `.ws` forms, the block-scaled forms and the forms of the ISA's examples that omit it) the
  mask is `4 * group size` zero words, so every lane is written. A missing collector qualifier is
  `discard`; the B collector of `.ws` is one of the buffers `b0` to `b3` (`bBuffer`), and the B
  collector without `.ws` is buffer 0. `.block32` and `.block16` are kept as written; which
  `.scale_vec::NX` they alias depends on the kind and K (§9.7.18.10.10.1).
  `TcMmaInstr.rule` gives THREAD-TC to the dense forms (no `.sp`, no `.block_scale`, no
  `.decompress::lut::b`, no `.ashift`) of `kind::i8`, `kind::f16`, `kind::tf32` and `kind::f8f6f4`,
  with any collector usage and with or without a zero-column mask. The other forms decode and have
  no rule, for these reasons. The block-scaled kinds (`kind::mxf8f6f4`, `kind::mxf4`,
  `kind::mxf4nvf4`): which Tensor Memory lanes and columns hold the scale factors of a row or column
  is given only by Figures 237 to 278 (§9.7.18.10.7.2, §9.7.18.10.7.3), and a rule needs, besides
  that layout, the scale factor reads of an MMA as Tensor Memory reads with their own sources,
  stability and conflicts, and the scale factor selectors of the instruction descriptor. `.sp`: the
  metadata layout in Tensor Memory is given only by Figures 287 to 292 (§9.7.18.10.9.4), and the
  metadata reads need the same Tensor Memory read rules. `.decompress::lut::b`: the lookup table
  layout and the compressed B layout are given only by Figures 279 to 282 (§9.7.18.10.8).
  `kind::ti16`: the text names the element type `.s1z4m11` ("a 16-bit signed integer with the range
  [-2 11 + 1, 2 11 - 1]") without its bit encoding. `.ashift`: the text says the rows of A are
  shifted down by one row "except for the last row in the Tensor Memory" without saying which rows
  form the matrix or what the first row then holds. A zero-column mask that generates a nonzero
  mask: Example 2 of §9.7.18.4.3 (Skip Span 2, Use Span 3, output `0b … 111 0000 111 0000`) starts
  with four used columns and continues with three zeroed columns, while Table 54 describes Skip Span
  as the count of used columns minus one and Use Span as the count of zeroed columns minus one, so
  the text and the example disagree on the mask.
-/

/-- The `.cta_group` qualifier: an aligned block of one or two cluster ranks. -/
inductive CtaGroup where
  | one | two
  deriving DecidableEq, Repr

def CtaGroup.size : CtaGroup → Nat
  | .one => 1
  | .two => 2

/-- The `.kind` qualifier of `tcgen05.mma`. -/
inductive MmaKind where
  | i8 | f16 | tf32 | f8f6f4 | mxf8f6f4 | mxf4 | mxf4nvf4 | ti16
  deriving DecidableEq, Repr

/-- A collector buffer usage (§9.7.18.10.10.1): `fill` loads the matrix into the buffer, `use`
and `lastuse` may read it from the buffer (`lastuse` then frees it), and `discard` frees it. -/
inductive MmaCollector where
  | fill | use | lastuse | discard
  deriving DecidableEq, Repr

/-- The usage reads the buffer: `use` or `lastuse`. -/
def MmaCollector.reuses : MmaCollector → Bool
  | .use | .lastuse => true
  | .fill | .discard => false

/-- The A operand of an MMA: a shared matrix descriptor, or a Tensor Memory address `[r+off]`. -/
inductive TcMmaA where
  | smem (desc : Opnd)
  | tmem (r : Nat) (off : Int)
  deriving DecidableEq, Repr

/-- The `.scale_vectorsize` qualifier as written. -/
inductive MmaScaleVec where
  | x1 | x2 | x4 | block16 | block32
  deriving DecidableEq, Repr

/-- `.block_scale` with its optional `.scale_vectorsize` and the scale factor addresses
`[scale-A-tmem]`, `[scale-B-tmem]`. -/
structure MmaBlockScale where
  vec : Option MmaScaleVec
  sfa : Nat × Int
  sfb : Nat × Int
  deriving DecidableEq, Repr

/-- A `tcgen05.mma` instruction (PROG-ISA-TC-MMA). -/
structure TcMmaInstr where
  group : CtaGroup
  /-- `.ws` (weight stationary, `cta_group::1` only). -/
  ws : Bool := false
  kind : MmaKind
  /-- The register of `[d-tmem]`. -/
  d : Nat
  a : TcMmaA
  bdesc : Opnd
  idesc : Opnd
  /-- The disable-output-lane words, `4 * group size` of them. -/
  mask : List Opnd
  enableD : Opnd
  /-- The 64-bit `zero-column-mask-desc` of `.ws`. -/
  zeroColumnMask : Option Opnd := none
  collectorA : MmaCollector := .discard
  collectorB : MmaCollector := .discard
  /-- The B collector buffer: `b<n>` of `.ws`, 0 otherwise. -/
  bBuffer : Nat := 0
  ashift : Bool := false
  /-- `.sp`: the address of `[sp-meta-tmem]`. -/
  sparse : Option (Nat × Int) := none
  scale : Option MmaBlockScale := none
  /-- `.decompress::lut::b`: the address of `[b-decompress-metadata]`. -/
  lut : Option (Nat × Int) := none
  deriving DecidableEq, Repr

/-- The forms that had their own constructors before the qualifiers above were represented:
`tcgen05.mma{.ws}` with A at `a`, no collector reuse and no zero-column mask. -/
def TcMmaInstr.dense (group : CtaGroup) (ws : Bool) (kind : MmaKind) (d : Nat) (a : TcMmaA)
    (bdesc idesc : Opnd) (mask : List Opnd) (enableD : Opnd) : TcMmaInstr :=
  { group, ws, kind, d, a, bdesc, idesc, mask, enableD }

namespace Decode
open PTX.Syntax

/-- The `.cta_group` qualifier. -/
def ctaGroup? : Option Isa.Token → Option CtaGroup
  | some .cta_group_1 => some .one
  | some .cta_group_2 => some .two
  | _ => none

/-- The `.kind` qualifier of `tcgen05.mma`. -/
def mmaKind? : Option Isa.Token → Option MmaKind
  | some .kind_i8 => some .i8
  | some .kind_f16 => some .f16
  | some .kind_tf32 => some .tf32
  | some .kind_f8f6f4 => some .f8f6f4
  | some .kind_mxf8f6f4 => some .mxf8f6f4
  | some .kind_mxf4 => some .mxf4
  | some .kind_mxf4nvf4 => some .mxf4nvf4
  | some .kind_ti16 => some .ti16
  | _ => none

/-- The `.collector::a::<op>` qualifier, `discard` when omitted. -/
def mmaCollectorA? : Option Isa.Token → Option MmaCollector
  | none | some .collector_a_discard => some .discard
  | some .collector_a_fill => some .fill
  | some .collector_a_use => some .use
  | some .collector_a_lastuse => some .lastuse
  | some _ => none

/-- The `.collector::b::<op>` or `.collector::b<n>::<op>` qualifier with its buffer,
`b0::discard` when omitted. -/
def mmaCollectorB? : Option Isa.Token → Option (MmaCollector × Nat)
  | none | some .collector_b_discard | some .collector_b0_discard => some (.discard, 0)
  | some .collector_b_fill | some .collector_b0_fill => some (.fill, 0)
  | some .collector_b_use | some .collector_b0_use => some (.use, 0)
  | some .collector_b_lastuse | some .collector_b0_lastuse => some (.lastuse, 0)
  | some .collector_b1_fill => some (.fill, 1) | some .collector_b1_use => some (.use, 1)
  | some .collector_b1_lastuse => some (.lastuse, 1)
  | some .collector_b1_discard => some (.discard, 1)
  | some .collector_b2_fill => some (.fill, 2) | some .collector_b2_use => some (.use, 2)
  | some .collector_b2_lastuse => some (.lastuse, 2)
  | some .collector_b2_discard => some (.discard, 2)
  | some .collector_b3_fill => some (.fill, 3) | some .collector_b3_use => some (.use, 3)
  | some .collector_b3_lastuse => some (.lastuse, 3)
  | some .collector_b3_discard => some (.discard, 3)
  | some _ => none

/-- The `.scale_vectorsize` qualifier: `.scale_vec::NX` or `.blockN`. -/
def mmaScaleVec? : Option Isa.Token → Option Isa.Token → Option (Option MmaScaleVec)
  | none, none => some none
  | some .scale_vec_1X, none => some (some .x1)
  | some .scale_vec_2X, none => some (some .x2)
  | some .scale_vec_4X, none => some (some .x4)
  | none, some .block16 => some (some .block16)
  | none, some .block32 => some (some .block32)
  | _, _ => none

/-- A Tensor Memory destination `[r]` or `[r+0]`: the register `r`. -/
def tmemDst (env : Env) : Operand → M Nat
  | .address [.register d] => reg env 32 (.register d)
  | .address [.offset "+" (.register d) (.literal t)] => do
    let .imm v ← literal t | throw s!"bad offset {t}"
    unless v = 0 do throw s!"unsupported Tensor Memory offset {t}"
    reg env 32 (.register d)
  | o => throw s!"unsupported Tensor Memory operand {repr o}"

/-- The `enable-input-d` operand of `tcgen05.mma`: a predicate register, or an integer constant
(§4.5.3: "integer constants may be used as predicates"). -/
def enableInput (env : Env) : Operand → M Opnd
  | .register r => .reg <$> reg env 1 (.register r)
  | .literal t => do
    let .imm v ← literal t | throw s!"enable-input-d constant {t}"
    pure (.imm v)
  | o => throw s!"unsupported enable-input-d {repr o}"

/-- The `tcgen05.mma` instruction of a recognized `tcgen05.mma` entry. -/
def TcMmaInstr.ofRaw (env : Env) (r : Isa.Raw) : M TcMmaInstr := do
  let some group := ctaGroup? (r.get .cta_group) | throw "tcgen05.mma .cta_group"
  let some kind := mmaKind? (r.get .kind) | throw "tcgen05.mma .kind"
  let some collectorA := mmaCollectorA? (r.get .collector_a) | throw "tcgen05.mma collector A"
  let some (collectorB, bBuffer) := mmaCollectorB? (r.get .collector_b)
    | throw "tcgen05.mma collector B"
  let a ← match opnd? r "a_tmem" with
    | some o => do let (ta, off) ← address env 32 o.op; pure (TcMmaA.tmem ta off)
    | none => do pure (TcMmaA.smem (← src env 64 (← arg r "a_desc")))
  let bdesc ← match opnd? r "b_desc" with
    | some o => src env 64 o.op
    | none => do src env 64 (← arg r "b_compressed_desc")
  let mask ← match opnd? r "disable_output_lane" with
    | some _ => do
      let ws ← srcs env 32 (← args r "disable_output_lane")
      unless ws.length = 4 * group.size do throw "tcgen05.mma disable-output-lane length"
      pure ws
    | none => pure (List.replicate (4 * group.size) (.imm 0))
  let zeroColumnMask ← match opnd? r "zero_col_mask" with
    | some o => some <$> src env 64 o.op
    | none => pure none
  let tmemOpnd (name : String) : M (Option (Nat × Int)) := match opnd? r name with
    | some o => some <$> address env 32 o.op
    | none => pure none
  let sparse ← tmemOpnd "sp_meta_tmem"
  let lut ← tmemOpnd "b_decompress_metadata"
  let scale ← if flag r .block_scale then do
      let some vec := mmaScaleVec? (r.get .scale_vec) (r.get .block_size)
        | throw "tcgen05.mma .scale_vectorsize"
      pure (some { vec, sfa := ← address env 32 (← arg r "sfa_tmem"),
                   sfb := ← address env 32 (← arg r "sfb_tmem") : MmaBlockScale })
    else pure none
  return { group, ws := flag r .ws, kind, d := ← tmemDst env (← arg r "d_tmem"), a, bdesc,
           idesc := ← src env 32 (← arg r "idesc"), mask,
           enableD := ← enableInput env (← arg r "enable_input_d"), zeroColumnMask,
           collectorA, collectorB, bBuffer, ashift := flag r .ashift, sparse, scale, lut }

end Decode

/-! ## PROG-ISA-TC-LD-RED — tcgen05.ld.red
Statement: A `tcgen05.ld.red` is a `tcgen05.ld` (`Op.tcLd`) with its reduction: `.min` or `.max`,
  the type `.u32`, `.s32` or `.f32`, the `.abs` and `.NaN` flags of the `.f32` form, and the
  destination `redval`. `.num` is at least `.x2`, and `redval` is not one of the loaded registers.

Defs: TcRedType, TcLdRed, Decode.TcLdRed.ofRaw

Source:
- §9.7.18.8.3: "tcgen05.ld.red.sync.aligned.shape3.num.redOp{.abs}{.NaN}.f32 r, redval, [taddr];"
- §9.7.18.8.3: "tcgen05.ld.red.sync.aligned.shape3.num.redOp.type r, redval, [taddr];"
- §9.7.18.8.3: ".redOp = { .min, .max } .type = { .u32, .s32 }"
- §9.7.18.8.3: "When .red qualifier is specified, .num modifier must be at least .x2 ."
- §6.4.3

Direction: representation

Applies: The `tcgen05_ld_red` and `tcgen05_ld_red_split` entries

Premises: The instruction is recognized by `Grammar.parse`; its registers are declared at 32 bits.

Effect: Representation; the rule is THREAD-TC-LD-RED.
  The text does not say whether `redval` may be one of the loaded registers; the decoder rejects
  that case (stricter).
-/

/-- The type of a `tcgen05.ld.red`. -/
inductive TcRedType where
  | u32 | s32 | f32
  deriving DecidableEq, Repr

/-- The reduction of a `tcgen05.ld.red` and its destination `redval`. -/
structure TcLdRed where
  isMax : Bool
  ty : TcRedType
  abs : Bool := false
  nan : Bool := false
  dst : Nat
  deriving DecidableEq, Repr

namespace Decode
open PTX.Syntax

/-- The reduction of a recognized `tcgen05.ld.red`. -/
def TcLdRed.ofRaw (env : Env) (r : Isa.Raw) : M TcLdRed := do
  let isMax ← match r.get .redop with
    | some .max => pure true
    | some .min => pure false
    | _ => throw "tcgen05.ld.red .redOp"
  let ty ← match r.get .type with
    | some .u32 => pure TcRedType.u32
    | some .s32 => pure .s32
    | some .f32 => pure .f32
    | _ => throw "tcgen05.ld.red .type"
  let abs := flag r .abs
  let nan := flag r .nan
  if ty ≠ .f32 ∧ (abs ∨ nan) then throw "tcgen05.ld.red .abs/.NaN need .f32"
  return { isMax, ty, abs, nan, dst := ← reg env 32 (← arg r "redval") }

end Decode

/-! ## PROG-ISA-TC-CP — tcgen05.cp shapes and decompression
Statement: A `tcgen05.cp` is its CTA group, its shape with the multicast that the shape requires
  (`.128x256b`, `.4x256b`, `.128x128b`, `.64x128b.warpx2::02_13`, `.64x128b.warpx2::01_23`,
  `.32x128b.warpx4`), the Tensor Memory address `[taddr]`, the source descriptor and the
  decompression `.b8x16.b6x16_p32` or `.b8x16.b4x16_p64` when written.

Defs: TcCpShape, TcCpFmt, Decode.tcCpShape?, Decode.tcCpFmt?

Source:
- §9.7.18.9.2: "tcgen05.cp.cta_group.shape{.multicast}{.dst_fmt.src_fmt} [taddr], s-desc;"
- §9.7.18.9.2: ".shape = { .128x256b, .4x256b, .128x128b, .64x128b**, .32x128b*** }"
- §9.7.18.9.2: ".64x128b requires .warpx2::02_13 or .warpx2::01_23 .32x128b requires .warpx4"
- §9.7.18.9.2: ".src_fmt = { .b6x16_p32 , .b4x16_p64 } .dst_fmt = { .b8x16 }"

Direction: representation

Applies: Every `tcgen05_cp` entry

Premises: The instruction is recognized by `Grammar.parse`.

Effect: Representation; the rule of a copy is THREAD-TC, its geometry THREAD-TC-CP-CELLS.
  A multicast written with another shape, or a shape written without the multicast it requires, is a
  decoding error; so is one of `.dst_fmt` and `.src_fmt` without the other (the table entry writes
  them as a pair).
-/

/-- A `tcgen05.cp` shape with its multicast: `.64x128b` with `.warpx2::02_13` (`warps0213`) or
`.warpx2::01_23`, and `.32x128b` with `.warpx4`. -/
inductive TcCpShape where
  | s128x256b
  | s128x128b
  | s64x128b (warps0213 : Bool)
  | s32x128b
  | s4x256b
  deriving DecidableEq, Repr

/-- The decompression of a `tcgen05.cp`: `.b8x16.b6x16_p32` (16 elements of 6 bits followed by
4 bytes of padding) or `.b8x16.b4x16_p64` (16 elements of 4 bits followed by 8 bytes of
padding), each to 16 bytes. -/
inductive TcCpFmt where
  | b6x16p32
  | b4x16p64
  deriving DecidableEq, Repr

namespace Decode

/-- The shape and multicast of a `tcgen05.cp`; an error for a multicast the shape does not
take. -/
def tcCpShape? : Option Isa.Token → Option Isa.Token → M TcCpShape
  | some .x128x256b, none => pure .s128x256b
  | some .x128x128b, none => pure .s128x128b
  | some .x64x128b, some .warpx2_02_13 => pure (.s64x128b true)
  | some .x64x128b, some .warpx2_01_23 => pure (.s64x128b false)
  | some .x32x128b, some .warpx4 => pure .s32x128b
  | some .x4x256b, none => pure .s4x256b
  | _, _ => throw "tcgen05.cp shape and multicast"

/-- The decompression of a `tcgen05.cp`: none, or `.b8x16` with a source format. -/
def tcCpFmt? : Option Isa.Token → Option Isa.Token → M (Option TcCpFmt)
  | none, none => pure none
  | some .b8x16, some .b6x16_p32 => pure (some .b6x16p32)
  | some .b8x16, some .b4x16_p64 => pure (some .b4x16p64)
  | _, _ => throw "tcgen05.cp .dst_fmt and .src_fmt"

end Decode

/-- THREAD-TC for the dense forms of `kind::i8`, `kind::f16`, `kind::tf32` and `kind::f8f6f4`
without `.ashift`, sparsity, block scaling or a lookup table; no rule otherwise. -/
def TcMmaInstr.rule (m : TcMmaInstr) : Option RuleId :=
  match m.kind, m.sparse, m.scale, m.lut, m.ashift with
  | .i8, none, none, none, false | .f16, none, none, none, false
  | .tf32, none, none, none, false | .f8f6f4, none, none, none, false => some .threadTc
  | _, _, _, _, _ => none

end PTX
