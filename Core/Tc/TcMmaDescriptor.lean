-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Instr

@[expose] public section

namespace PTX.TcMma

/-! ## THREAD-TC-MMA-DESCRIPTOR — dense instruction descriptor and shape
Statement: The 32-bit instruction descriptor of a dense `tcgen05.mma` decodes into the element
  types, M, N and the negate and transpose flags, and is accepted only when the types fit the
  `.kind`, M and N form a shape of Table 48 for the CTA group and `.ws` mode, and the reserved,
  sparsity, K-dimension and shift bits are zero. K is fixed by the kind at 32 bytes per operand row:
  32 8-bit, 16 16-bit or 8 TF32 elements, or 32 elements of `kind::f8f6f4` in one-byte containers.

Defs: TcMma.F8f6f4, TcMma.F8f6f4.eightBit, TcMma.F8f6f4.ofCode, TcMma.Kind, TcMma.Kind.width,
  TcMma.Kind.k, TcMma.Descriptor, TcMma.shapeOk, TcMma.typesOk, TcMma.transposeOk, TcMma.Valid,
  TcMma.validDecidable, TcMma.decodeKind, TcMma.decode

Source:
- §9.7.18.2.1 Table 48
- §9.7.18.4.2 Table 51
- §9.7.18.10.1: "For .kind::tf32 , the transpose operations on matrices A and B are supported only
    with 128B swizzling mode with 32B swizzle-atomicity."
- §9.7.18.10.1 (Table 62)
- §9.7.18.10.1 Table 63 (N shapes for 8-bit transpose B, cta_group 1): "16 <= N <= 256, step 16"
- §9.7.18.10.1 Table 63 (N shapes for 8-bit transpose B, cta_group 2): "32 <= N <= 256, step 32"
- §9.7.18.10.3 Table 65
- §9.7.18.10.4.4: "Dense-K dimension Padding needed after 16 elements 32 Yes 64 No"
- §9.7.18.9.1.1: "A contiguous set of 16 elements of 4-bits each followed by 8 bytes of padding"
- §9.7.18.9.1.2: "A contiguous set of 16 elements of 6-bits each followed by 4 bytes of padding"
- EXT-TCFIG

Direction: scope

Applies: Dense tcgen05.mma.cta_group::{1,2}.kind::{i8,f16,tf32,f8f6f4} and
  tcgen05.mma.ws.cta_group::1.kind::{i8,f16,tf32,f8f6f4}

Premises: The 32-bit descriptor has documented type and shape fields and zero reserved, sparse,
  K-dimension and shift bits; the saturate bit is zero except for kind::i8. Dense sparsity-selector
  bits are ignored. kind::f16 inputs are both FP16 or both BF16 and FP16 output requires FP16
  inputs; kind::i8 inputs are U8 or S8 with S32 output and no negation; kind::tf32 inputs are TF32
  (type 2) with F32 output; kind::f8f6f4 inputs are E4M3, E5M2, E2M3, E3M2 or E2M1, each operand its
  own, with FP16 or FP32 output.

Effect: Instruction-descriptor decoding. Floating numerical treatment belongs to the chosen
  arithmetic profile. With `.ws`, M is one of 32, 64 and 128 and N is one of 64, 128 and 256. Bits 2
  (sparsity), 6 and 23 (reserved), 29 (K dimension: the dense value 0 of Table 51) and 30–31 (the
  `.ws` B-reuse shift field) must be zero, and no bit above 31 may be set. Bits 0–1 (the sparsity
  selector, meaningful only when sparse) are ignored, and bit 3 (saturate) is read for kind::i8 and
  must be zero for the other kinds. The remaining fields are bits 4–5 (D type), 7–9 (A type), 10–12
  (B type), 13–16 (negation and transposition of A and B), 17–22 (N >> 3) and 24–28 (M >> 4). Table
  51 lets bits 30–31 select a nonzero B-reuse shift for `.ws` and says nothing about them for the
  other forms, and the decoder rejects every nonzero value, which is stricter than the text for
  every form. kind::tf32 and kind::f8f6f4 have the shapes of kind::f16 (Table 48). Bit 29 is 0, so
  kind::f8f6f4 has its dense K of 32 elements; K = 64 (bit 29 set, sm_107f only) has no rule.
  Transposition (`transposeOk`): kind::i8 and the 8-bit types of kind::f8f6f4 with transposed B take
  the N shapes of Table 63. A 6- or 4-bit operand of kind::f8f6f4 is not transposed: Table 65 lists
  transposed layouts for 8-, 16- and 32-bit types only. kind::tf32 may be transposed only with 128B
  swizzling with 32B atomicity and the 8- and 16-bit kinds not with it (§9.7.18.10.3 Table 65). The
  swizzle is a field of the shared descriptor, so this descriptor accepts a transposed kind::tf32
  and the pairing is enforced by THREAD-TC-SHARED-ADDRESS, which yields an address for an MN-major
  operand exactly when the 32B-atomic mode is paired with 4-byte elements.
-/
/-- An element type of `kind::f8f6f4` (Table 51: "E4M3 = 0 E5M2 = 1 E2M3 = 3 E3M2 = 4 E2M1 =
5"). -/
inductive F8f6f4 where
  | e4m3 | e5m2 | e2m3 | e3m2 | e2m1
  deriving DecidableEq, Repr

/-- The 8-bit types E4M3 and E5M2. -/
def F8f6f4.eightBit : F8f6f4 → Bool
  | .e4m3 | .e5m2 => true
  | .e2m3 | .e3m2 | .e2m1 => false

/-- The type of an `atype` or `btype` code of `kind::f8f6f4`. -/
def F8f6f4.ofCode : Nat → Option F8f6f4
  | 0 => some .e4m3 | 1 => some .e5m2 | 3 => some .e2m3 | 4 => some .e3m2 | 5 => some .e2m1
  | _ => none

/-- The kind of a dense MMA with its element types, given by the `.kind` qualifier and the type
fields of the instruction descriptor. -/
inductive Kind where
  /-- `kind::i8`: unsigned or signed 8-bit inputs, 32-bit integer D, optionally saturating
  (descriptor bit 3). -/
  | i8 (signedA signedB saturate : Bool)
  /-- `kind::f16`: FP16 or BF16 inputs, FP16 or FP32 D. -/
  | f16 (input output : FloatFmt)
  /-- `kind::tf32`: TF32 inputs in 32-bit containers, FP32 D. -/
  | tf32
  /-- `kind::f8f6f4`: 8-, 6- or 4-bit floating A and B in one-byte containers, FP16 or FP32 D. -/
  | f8f6f4 (a b : F8f6f4) (output : FloatFmt)
  deriving DecidableEq, Repr

/-- Bytes per input element; the one-byte container of a `kind::f8f6f4` element. -/
def Kind.width : Kind → Nat
  | .i8 .. => 1
  | .f16 .. => 2
  | .tf32 => 4
  | .f8f6f4 .. => 1

/-- Contraction elements per dense issue. -/
def Kind.k : Kind → Nat
  | .i8 .. => 32
  | .f16 .. => 16
  | .tf32 => 8
  | .f8f6f4 .. => 32

/-- A decoded instruction descriptor of a dense `tcgen05.mma` (§9.7.18.4.2 Table 51), together
with the CTA group and `.ws` mode of the instruction. -/
structure Descriptor where
  /-- The `.cta_group` of the instruction. -/
  group : CtaGroup
  /-- The kind and element types. -/
  kind : Kind
  /-- The M dimension: bits 24 to 28 times 16. -/
  m : Nat
  /-- The N dimension: bits 17 to 22 times 8. -/
  n : Nat
  /-- Negate A (bit 13). -/
  negateA : Bool
  /-- Negate B (bit 14). -/
  negateB : Bool
  /-- Transpose A (bit 15): A is MN-major. -/
  transposeA : Bool
  /-- Transpose B (bit 16): B is MN-major. -/
  transposeB : Bool
  /-- Weight-stationary issue (`tcgen05.mma.ws`, cta_group::1 only). -/
  ws : Bool
  deriving DecidableEq, Repr

/-- Dense shapes of Table 48 with a represented D layout. -/
def shapeOk : CtaGroup → Bool → Kind → Nat → Nat → Bool
  | .one, true, _, m, n => (m = 32 ∨ m = 64 ∨ m = 128) ∧ (n = 64 ∨ n = 128 ∨ n = 256)
  | .two, true, _, _, _ => false
  | .one, false, .f16 .., m, n | .one, false, .tf32, m, n | .one, false, .f8f6f4 .., m, n =>
    (m = 64 ∨ m = 128) ∧ 8 ≤ n ∧ n ≤ 256 ∧ n % 8 = 0
  | .two, false, .f16 .., m, n | .two, false, .tf32, m, n | .two, false, .f8f6f4 .., m, n =>
    (m = 128 ∨ m = 256) ∧ 16 ≤ n ∧ n ≤ 256 ∧ n % 16 = 0
  | .one, false, .i8 .., m, n =>
    (m = 64 ∨ m = 128) ∧ ((8 ≤ n ∧ n ≤ 32 ∧ n % 8 = 0) ∨ (32 < n ∧ n ≤ 256 ∧ n % 16 = 0))
  | .two, false, .i8 .., m, n => (m = 128 ∨ m = 256) ∧ 32 ≤ n ∧ n ≤ 256 ∧ n % 32 = 0

/-- Type and negation fields allowed for the kind (Table 51). -/
def typesOk (d : Descriptor) : Bool :=
  match d.kind with
  | .i8 .. => !d.negateA && !d.negateB
  | .f16 input output =>
    (input = .f16 ∨ input = .bf16) ∧ (output = .f16 ∨ output = .f32) ∧
      (output = .f16 → input = .f16)
  | .tf32 => true
  | .f8f6f4 _ _ output => output = .f16 ∨ output = .f32

/-- Transposition limits of §9.7.18.10.1 (Tables 62, 63). -/
def transposeOk (d : Descriptor) : Bool :=
  match d.kind with
  | .i8 .. => !d.transposeB ||
    match d.group with
    | .one => 16 ≤ d.n && d.n ≤ 256 && d.n % 16 == 0
    | .two => 32 ≤ d.n && d.n ≤ 256 && d.n % 32 == 0
  | .f16 .. => true
  | .tf32 => true
  | .f8f6f4 a b _ => (!d.transposeA || a.eightBit) && (!d.transposeB || b.eightBit &&
    match d.group with
    | .one => 16 ≤ d.n && d.n ≤ 256 && d.n % 16 == 0
    | .two => 32 ≤ d.n && d.n ≤ 256 && d.n % 32 == 0)

/-- The decoded descriptor is a supported dense MMA: a shape of Table 48 for its CTA group and
`.ws` mode, types and negation allowed for its kind, and transposition within the limits of
Table 63. -/
def Valid (d : Descriptor) : Prop :=
  shapeOk d.group d.ws d.kind d.m d.n = true ∧ typesOk d = true ∧ transposeOk d = true

instance validDecidable (d : Descriptor) : Decidable (Valid d) := by
  unfold Valid
  infer_instance

/-- The kind given by the instruction's `.kind` and the type fields. -/
def decodeKind : MmaKind → Nat → Nat → Nat → Nat → Option Kind
  | .i8, saturate, aType, bType, dType =>
    if dType = 2 ∧ aType ≤ 1 ∧ bType ≤ 1 then some (.i8 (aType = 1) (bType = 1) (saturate = 1))
    else none
  | .f16, saturate, aType, bType, dType =>
    if saturate = 0 ∧ aType ≤ 1 ∧ bType = aType ∧ dType ≤ 1 then
      some (.f16 (if aType = 0 then .f16 else .bf16) (if dType = 0 then .f16 else .f32))
    else none
  | .tf32, saturate, aType, bType, dType =>
    if saturate = 0 ∧ aType = 2 ∧ bType = 2 ∧ dType = 1 then some .tf32 else none
  | .f8f6f4, saturate, aType, bType, dType =>
    match F8f6f4.ofCode aType, F8f6f4.ofCode bType with
    | some a, some b =>
      if saturate = 0 ∧ dType ≤ 1 then some (.f8f6f4 a b (if dType = 0 then .f16 else .f32))
      else none
    | _, _ => none
  | .mxf8f6f4, _, _, _, _ | .mxf4, _, _, _, _ | .mxf4nvf4, _, _, _, _ | .ti16, _, _, _, _ => none

/-- Decode the 32-bit instruction descriptor `x` of a dense MMA with CTA group `group`, `.ws`
mode `ws` and `.kind` `q`; `none` when a reserved, sparsity, K-dimension or shift bit is set or
the kind, types or shape are not supported. -/
def decode (group : CtaGroup) (ws : Bool) (q : MmaKind) (x : Nat) : Option Descriptor :=
  match decodeKind q (x / 2 ^ 3 % 2) (x / 2 ^ 7 % 8) (x / 2 ^ 10 % 8) (x / 2 ^ 4 % 4) with
  | none => none
  | some kind =>
    let d : Descriptor := {
      group, kind
      m := x / 2 ^ 24 % 32 * 16
      n := x / 2 ^ 17 % 64 * 8
      negateA := x / 2 ^ 13 % 2 = 1
      negateB := x / 2 ^ 14 % 2 = 1
      transposeA := x / 2 ^ 15 % 2 = 1
      transposeB := x / 2 ^ 16 % 2 = 1
      ws }
    if x / 4 % 2 = 0 ∧ x / 64 % 2 = 0 ∧
        x / 2 ^ 23 % 2 = 0 ∧ x / 2 ^ 29 = 0 ∧ Valid d then some d else none

end PTX.TcMma
