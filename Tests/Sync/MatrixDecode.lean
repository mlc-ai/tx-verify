-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! Decoding of the warp-level matrix instructions and their rules (PROG-ISA-MATRIX): every
operation decodes to `Op.matrix`, the forms of the manual's syntax lines have THREAD-MATRIX or
THREAD-MMA-SYNC, and the forms the table admits beyond them have no rule. -/
namespace PTX.Tests.MatrixDecode
open PTX.Syntax

-- `%r0` .. `%r7` are registers 0 to 7 (32-bit), `%rd0` is register 8 (64-bit), `%f0` .. `%f3`
-- registers 9 to 12 (32-bit), `%d0` .. `%d7` registers 13 to 20 (64-bit).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 1, 64⟩, ⟨"%f".toList, 4, 32⟩,
      ⟨"%d".toList, 8, 64⟩],
    labels := [], params := [] }

private def p : Operand := .address [.register "%rd0"]

/-! ## `ldmatrix`, `stmatrix`, `movmatrix` -/

private def r0 : Operand := .register "%r0"
private def r1 : Operand := .register "%r1"
private def r2 : Operand := .register "%r2"
private def r3 : Operand := .register "%r3"
private def r4 : Operand := .register "%r4"
private def r5 : Operand := .register "%r5"
private def r6 : Operand := .register "%r6"
private def r7 : Operand := .register "%r7"
private def fs : Operand :=
  .vector [.register "%f0", .register "%f1", .register "%f2", .register "%f3"]

private def ldx4 : MatrixInstr :=
  { op := .move { store := false, shape := .m8n8, num := 4, trans := false, fmt := .b16 },
    space := some (.shared .cta), addr := some ⟨.reg 8 64, 0⟩, dsts := [0, 1, 2, 3] }

example : Decode.op env "ldmatrix.sync.aligned.m8n8.x4.shared.b16" [.vector [r0, r1, r2, r3], p] =
    .ok (.matrix ldx4) := rfl
example : ldx4.rule = some .threadMatrix := rfl
-- Generic addressing and `.trans`.
example : (Decode.op env "ldmatrix.sync.aligned.m8n8.x2.trans.b16" [.vector [r0, r1], p]).map
    Op.rule = .ok (some .threadMatrix) := rfl
-- `.m16n16.x1.trans.b8` has two destination registers.
example : (Decode.op env "ldmatrix.sync.aligned.m16n16.x1.trans.shared::cta.b8"
    [.vector [r0, r1], p]).map Op.rule = .ok (some .threadMatrix) := rfl
-- The expanded `.b8x16` forms of the syntax lines: `.m8n16` without `.trans`, `.m16n16` with it.
example : (Decode.op env "ldmatrix.sync.aligned.m8n16.x1.shared.b8x16.b6x16_p32"
    [.vector [r0], p]).map Op.rule = .ok (some .threadMatrix) := rfl
example : (Decode.op env "ldmatrix.sync.aligned.m16n16.x1.trans.b8x16.b4x16_p64"
    [.vector [r0, r1], p]).map Op.rule = .ok (some .threadMatrix) := rfl
-- `.m8n16` with `.trans` is on no syntax line and is rejected.
example : (Decode.op env "ldmatrix.sync.aligned.m8n16.x1.trans.shared.b8x16.b6x16_p32"
    [.vector [r0], p]).isOk = false := rfl
-- `.s8.s4` decodes and has no rule.
example : (Decode.op env "ldmatrix.sync.aligned.m8n16.x1.shared.s8.s4" [.vector [r0], p]).map
    Op.rule = .ok none := rfl
-- A destination count other than the shape's is rejected by the grammar.
example : (Decode.op env "ldmatrix.sync.aligned.m8n8.x2.b16" [.vector [r0], p]).isOk = false :=
  rfl
-- `.x4` is not a `.num` of `.m16n16`.
example : (Decode.op env "ldmatrix.sync.aligned.m16n16.x4.trans.b8"
    [.vector [r0, r1, r2, r3, r4, r5, r6, r7], p]).isOk = false := rfl

example : (Decode.op env "stmatrix.sync.aligned.m8n8.x1.trans.shared.b16" [p, .vector [r0]]).map
    Op.rule = .ok (some .threadMatrix) := rfl
example : (Decode.op env "stmatrix.sync.aligned.m16n8.x2.trans.shared::cta.b8"
    [p, .vector [r0, r1]]).map Op.rule = .ok (some .threadMatrix) := rfl
example : Decode.op env "movmatrix.sync.aligned.m8n8.trans.b16" [r0, r1] =
    .ok (.matrix { op := .transpose, dsts := [0], srcs := [.reg 1] }) := rfl
example : MatrixInstr.rule { op := .transpose, dsts := [0], srcs := [.reg 1] } =
    some .threadMatrix := rfl

-- Every matrix instruction is aligned, performs an event and needs a warp-uniform guard.
example : Op.aligned (.matrix ldx4) = true := rfl
example : Op.isLocal (.matrix ldx4) = false := rfl
example : Op.uniform (.matrix ldx4) = true := rfl

/-! ## `mma` and `mma.sp` -/

private def tF16 : MmaTypes :=
  { a := .float .f16, b := .float .f16, c := .float .f32, d := .float .f32 }

-- `.m16n8k16.row.col.f32.f16.f16.f32`: four A, two B, four C and four D registers.
private def mmaF16 : MatrixInstr :=
  { op := .mma { m := 16, n := 8, k := 16, types := tF16 }, dsts := [9, 10, 11, 12],
    srcs := [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 9, .reg 10, .reg 11, .reg 12] }

example : Decode.op env "mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32"
    [fs, .vector [r0, r1, r2, r3], .vector [r4, r5], fs] = .ok (.matrix mmaF16) := rfl
example : mmaF16.rule = some .threadMma := rfl
-- The four-MMA form with a column-major A.
example : (Decode.op env "mma.sync.aligned.m8n8k4.col.row.f16.f16.f16.f16"
    [.vector [r0, r1, r2, r3], .vector [r4, r5], .vector [r6, r7], .vector [r0, r1, r2, r3]]).map
    Op.rule = .ok (some .threadMma) := rfl
-- Integer, single-bit and `.f64` forms.
example : (Decode.op env "mma.sync.aligned.m8n8k16.row.col.satfinite.s32.s8.u8.s32"
    [.vector [r0, r1], .vector [r2], .vector [r3], .vector [r4, r5]]).map Op.rule =
    .ok (some .threadMma) := rfl
example : (Decode.op env "mma.sync.aligned.m16n8k256.row.col.s32.b1.b1.s32.xor.popc"
    [.vector [r0, r1, r2, r3], .vector [r4, r5, r6, r7], .vector [r0, r1],
      .vector [r4, r5, r6, r7]]).map Op.rule = .ok (some .threadMma) := rfl
example : (Decode.op env "mma.sync.aligned.m8n8k4.row.col.f64.f64.f64.f64"
    [.vector [.register "%d0", .register "%d1"], .vector [.register "%d2"],
      .vector [.register "%d3"], .vector [.register "%d4", .register "%d5"]]).map Op.rule =
    .ok (some .threadMma) := rfl
-- `mma.sp::ordered_metadata` with the metadata register and the selector.
example : (Decode.op env "mma.sp::ordered_metadata.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32"
    [fs, .vector [r0, r1], .vector [r2, r3], fs, r4, .literal "1"]).map Op.rule =
    .ok (some .threadMma) := rfl
-- A register count that differs from the shape's has no rule.
example : MatrixInstr.rule { mmaF16 with srcs := mmaF16.srcs.drop 1 } = none := rfl
-- A shape without fragments in the manual has no rule.
example : MatrixInstr.rule { mmaF16 with op := .mma { m := 16, n := 8, k := 32, types := tF16 } } =
    none := rfl

/-! ## Forms without a representation -/

-- `spcompress` belongs to the family and has no representation.
example : (Decode.op env "spcompress.b8.b2.sp::2:4.x1"
    [.vector [r0], .vector [r1], .vector [r2, r3], r4]).map Op.rule = .ok none := rfl

end PTX.Tests.MatrixDecode
