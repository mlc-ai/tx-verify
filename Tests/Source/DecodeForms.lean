-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode

/-! Decoder checks of PROG-DECODE: repeated destination registers (§6.4.3 UB), integer
constants at floating-point types (§9.4 Table 26), 128-bit constants and parameters, the type
and range of integer literals (§4.5.1) and their unary minus (§4.5.5), and the §9.7 `.type`
lists. Each rejected form is next to an accepted neighbour. -/
namespace PTX.Tests.DecodeForms
open PTX.Syntax

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 8, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%q".toList, 2, 128⟩,
      ⟨"%f".toList, 2, 32⟩, ⟨"%p".toList, 1, 1⟩, ⟨"%h".toList, 2, 16⟩, ⟨"%c".toList, 2, 8⟩],
    labels := [], params := [("p32", 32), ("p128", 128)] }


/-! ## §6.4.3: a destination vector names each register once -/

-- `ld.shared.v2.b32 {%r5, %r5}, [%r2]`
example : (Decode.op env "ld.shared.v2.b32" [.vector [.register "%r5", .register "%r5"],
    .address [.register "%r2"]]).isOk = false := rfl
example : Decode.op env "ld.shared.v2.b32" [.vector [.register "%r5", .register "%r6"],
    .address [.register "%r2"]] =
    .ok (.mem {
      kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
      vec := 2, addr := ⟨.reg 2 32, 0⟩, dsts := [some 5, some 6] }) := rfl
-- `mov.b64 {%r1, %r1}, %rd0`
example : (Decode.op env "mov.b64" [.vector [.register "%r1", .register "%r1"],
    .register "%rd0"]).isOk = false := rfl
example : Decode.op env "mov.b64" [.vector [.register "%r1", .register "%r2"], .register "%rd0"] =
    .ok (.move ⟨.unpack, .int .b 64, [some 1, some 2], [.reg 8]⟩) := rfl
-- `tcgen05.ld … {%r0, %r1, %r0, %r3}, [%r4]`
example : (Decode.op env "tcgen05.ld.sync.aligned.32x32b.x4.b32"
    [.vector [.register "%r0", .register "%r1", .register "%r0", .register "%r3"],
      .address [.register "%r4"]]).isOk = false := rfl
example : Decode.op env "tcgen05.ld.sync.aligned.32x32b.x4.b32"
    [.vector [.register "%r0", .register "%r1", .register "%r2", .register "%r3"],
      .address [.register "%r4"]] = .ok (.tcLd [0, 1, 2, 3] 4) := rfl

/-! ## §9.4 Table 26: an integer constant at a floating-point type is invalid -/

example : (Decode.op env "mov.f32" [.register "%f0", .literal "1"]).isOk = false := rfl
example : Decode.op env "mov.f32" [.register "%f0", .literal "0f3F800000"] =
    .ok (.move ⟨.scalar, .float .f32, [some 12], [.f32imm 0x3F800000]⟩) := rfl
example : Decode.op env "mov.b32" [.register "%f0", .literal "1"] =
    .ok (.move ⟨.scalar, .int .b 32, [some 12], [.imm 1]⟩) := rfl
example : (Decode.op env "st.global.f32" [.address [.register "%rd0"], .literal "1"]).isOk =
    false := rfl
example : (Decode.op env "selp.f32"
    [.register "%f0", .literal "1", .register "%f1", .register "%p0"]).isOk = false := rfl
example : (Decode.op env "add.f32" [.register "%f0", .register "%f1", .literal "1"]).isOk = false :=
  rfl

/-! ## §4.5.1: constants are 64-bit; 128-bit parameters are not read -/

-- a literal is `.s64` unless its value needs `.u64` or it has the `U` suffix; a value outside
-- `.u64` is not a constant
example : (Decode.op env "mov.u64" [.register "%rd0", .literal "18446744073709551616"]).isOk =
    false :=
  rfl
example : (Decode.op env "mov.u64" [.register "%rd0", .literal "0x10000000000000000"]).isOk =
    false :=
  rfl
example : (Decode.op env "mov.u64" [.register "%rd0", .literal "18446744073709551616U"]).isOk =
    false :=
  rfl
example : Decode.op env "mov.u64" [.register "%rd0", .literal "18446744073709551615"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 8], [.imm 18446744073709551615]⟩) := rfl
example : Decode.op env "mov.u64" [.register "%rd0", .literal "42U"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 8], [.imm 42]⟩) :=
  rfl
-- the suffix is the letter `U` (§4.5.1)
example : (Decode.op env "mov.u64" [.register "%rd0", .literal "42u"]).isOk = false := rfl
-- §4.5.5: unary minus keeps the literal's type; a `.u64` operand is negated modulo `2^64`
example : Decode.op env "mov.s64" [.register "%rd0", .literal "-1"] =
    .ok (.move ⟨.scalar, .int .s 64, [some 8], [.imm (-1)]⟩) :=
  rfl
example : Decode.op env "mov.u64" [.register "%rd0", .literal "-1U"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 8], [.imm 18446744073709551615]⟩) := rfl
example : Decode.op env "mov.u64" [.register "%rd0", .literal "-0xfabc123400000000"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 8], [.imm 0x0543edcc00000000]⟩) := rfl
example : Decode.op env "mov.s64" [.register "%rd0", .literal "-9223372036854775807"] =
    .ok (.move ⟨.scalar, .int .s 64, [some 8], [.imm (-9223372036854775807)]⟩) := rfl
-- `9223372036854775808` is not representable in `.s64`, so it and its negation are `.u64`
example : Decode.op env "mov.s64" [.register "%rd0", .literal "-9223372036854775808"] =
    .ok (.move ⟨.scalar, .int .s 64, [some 8], [.imm 9223372036854775808]⟩) := rfl
example : Decode.op env "mov.s64" [.register "%rd0", .literal "-9223372036854775809"] =
    .ok (.move ⟨.scalar, .int .s 64, [some 8], [.imm 9223372036854775807]⟩) := rfl
example : Decode.op env "mov.u64" [.register "%rd0", .literal "-0U"] =
    .ok (.move ⟨.scalar, .int .u 64, [some 8], [.imm 0]⟩) :=
  rfl
example : (Decode.op env "mov.u64" [.register "%rd0", .literal "-18446744073709551616"]).isOk =
    false := rfl
-- other constant expressions are not supported
example : (Decode.op env "mov.s64" [.register "%rd0", .literal "+1"]).isOk = false := rfl
example : (Decode.op env "mov.s64" [.register "%rd0", .literal "--1"]).isOk = false := rfl

example : (Decode.op env "st.shared.b128" [.address [.register "%r0"], .literal "-1"]).isOk =
    false := rfl
example : Decode.op env "st.shared.b128" [.address [.register "%r0"], .register "%q0"] =
    .ok (.mem {
      kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 128,
      addr := ⟨.reg 0 32, 0⟩, srcs := [.reg 10] }) := rfl
example : (Decode.op env "ld.param.b128" [.register "%q0", .address [.symbol "p128"]]).isOk =
    false :=
  rfl
example : Decode.op env "ld.param.b32" [.register "%r0", .address [.symbol "p32"]] =
    .ok (.mem {
      kind := .load, space := some .param, sem := .weak, elem := .int .b 32,
      addr := ⟨.param "p32" false, 0⟩, dsts := [some 0] }) :=
  rfl

/-! ## §9.7 `.type` lists -/

-- and/or: `.b16 .b32 .b64`.
example : (Decode.op env "and.b128" [.register "%q0", .register "%q1", .register "%q1"]).isOk =
    false :=
  rfl
example : (Decode.op env "or.b8" [.register "%c0", .register "%c1", .register "%c1"]).isOk =
    false :=
  rfl
-- add: `.u16 … .s64`, no bit-size type and no 8-bit type.
example : (Decode.op env "add.b32" [.register "%r0", .register "%r1", .register "%r2"]).isOk =
    false := rfl
example : (Decode.op env "add.u8" [.register "%c0", .register "%c1", .register "%c1"]).isOk =
    false :=
  rfl
example : Decode.op env "add.u32" [.register "%r0", .register "%r1", .register "%r2"] =
    .ok (.int ⟨.add, .int .u 32, false, [some 0], [.reg 1, .reg 2]⟩) := rfl
-- setp: 16- to 64-bit integer types.
example : (Decode.op env "setp.eq.b128" [.register "%p0", .register "%q0", .register "%q1"]).isOk =
    false := rfl
-- scalar mov: no `.b8` and no `.b128`; pack and unpack are bit-size only.
example : (Decode.op env "mov.b8" [.register "%c0", .register "%c1"]).isOk = false := rfl
example : (Decode.op env "mov.b128" [.register "%q0", .register "%q1"]).isOk = false := rfl
example : (Decode.op env "mov.u64" [.vector [.register "%r1", .register "%r2"],
    .register "%rd0"]).isOk = false := rfl
example : Decode.op env "mov.b128" [.vector [.register "%rd0", .register "%rd1"], .register "%q0"] =
    .ok (.move ⟨.unpack, .int .b 128, [some 8, some 9], [.reg 10]⟩) := rfl
-- ld/st: no `.f16`; `.v4` of a 64-bit type only in global memory.
example : (Decode.op env "ld.global.f16" [.register "%h0", .address [.register "%rd0"]]).isOk =
    false := rfl
example : (Decode.op env "ld.shared.v4.b64" [.vector [.register "%rd0", .register "%rd1",
    .register "%rd0", .register "%rd1"], .address [.register "%r0"]]).isOk =
    false := rfl
example : (Decode.op env "st.shared.v4.b64" [.address [.register "%r0"],
    .vector [.register "%rd0", .register "%rd1", .register "%rd0", .register "%rd1"]]).isOk =
    false := rfl
example : (Decode.op env "st.global.v4.b64" [.address [.register "%rd0"],
    .vector [.register "%rd0", .register "%rd1", .register "%rd0", .register "%rd1"]]).isOk =
    true := rfl
-- fma.f32 needs a rounding modifier; the approximate forms take none.
example : (Decode.op env "fma.ftz.f32"
    [.register "%f0", .register "%f1", .register "%f1", .register "%f1"]).isOk = false := rfl
example : (Decode.op env "fma.rn.ftz.f32"
    [.register "%f0", .register "%f1", .register "%f1", .register "%f1"]).isOk = true := rfl
example : (Decode.op env "div.approx.rn.f32"
    [.register "%f0", .register "%f1", .register "%f1"]).isOk = false := rfl
example : (Decode.op env "div.approx.ftz.f32"
    [.register "%f0", .register "%f1", .register "%f1"]).isOk = true := rfl

/-! ## §6.4.3: a one-element brace list stands for its register -/

-- `ld.global.b32 {%r1}, [%rd0]` is `ld.global.b32 %r1, [%rd0]`; the list is not a `.v2`.
example : Decode.op env "ld.global.b32" [.vector [.register "%r1"], .address [.register "%rd0"]] =
    Decode.op env "ld.global.b32" [.register "%r1", .address [.register "%rd0"]] := rfl
example : (Decode.op env "ld.global.b32" [.vector [.register "%r1"],
    .address [.register "%rd0"]]).isOk = true := rfl
example : (Decode.op env "ld.global.b32" [.vector [.register "%r1", .register "%r2"],
    .address [.register "%rd0"]]).isOk = false := rfl
-- `st.global.b32 [%rd0 + 0], {%r1}` is `st.global.b32 [%rd0 + 0], %r1`.
example : Decode.op env "st.global.b32" [.address [.register "%rd0"], .vector [.register "%r1"]] =
    Decode.op env "st.global.b32" [.address [.register "%rd0"], .register "%r1"] := rfl
example : (Decode.op env "st.global.b32" [.address [.register "%rd0"],
    .vector [.register "%r1"]]).isOk = true := rfl
-- A register group still takes exactly its lanes.
example : (Decode.op env "ld.shared.v2.b32" [.vector [.register "%r5"],
    .address [.register "%r2"]]).isOk = false := rfl

end PTX.Tests.DecodeForms
