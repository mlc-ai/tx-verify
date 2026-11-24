-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode

/-! Decoding of the `float` family (PROG-ISA-FLOAT): one example for each of the 53 entries,
together using every rounding modifier, `.ftz`, `.sat`, `.relu`, `.oob`, `.NaN`, `.xorsign`, `.abs`,
every `testp` property, every floating comparison operator, every `BoolOp`, the `p|q` pair, the
modes `approx`, `full` and `rn` to `rp`, and the types `f16`, `bf16`, `f32`, `f64`, `f16x2`,
`bf16x2` and `f32x2`; the operand widths; the mixed-precision forms with their source types; the
`set` with an integer source type; the rule of every decoded form (`FloatInstr.rule`); and the
rejected forms. -/
namespace PTX.Tests.FloatDecode
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 4, 64⟩, ⟨"%rs".toList, 4, 16⟩,
      ⟨"%p".toList, 4, 1⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd3 = 4..7, %rs0..%rs3 = 8..11, %p0..%p3 = 12..15
private def r (n : String) : Syntax.Operand := .register n

private def f16 : FTy := { fmt := .f16 }
private def bf16 : FTy := { fmt := .bf16 }
private def f32 : FTy := { fmt := .f32 }
private def f64 : FTy := { fmt := .f64 }
private def f16x2 : FTy := { fmt := .f16, lanes := 2 }
private def bf16x2 : FTy := { fmt := .bf16, lanes := 2 }
private def f32x2 : FTy := { fmt := .f32, lanes := 2 }

/-- The rule of a decoded instruction (`none` when it does not decode). -/
private def rule (op : String) (args : List Syntax.Operand) : Option (Option RuleId) :=
  (Op.rule <$> Decode.op env op args).toOption


/-! ## Arithmetic (§9.7.3.3 to §9.7.3.8) -/

example : Decode.op env "add.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .add, ty := f32, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "add.rm.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .add, ty := f64, rnd := some .rm, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "add.rp.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .add, ty := f32x2, rnd := some .rp, ftz := true, dsts := [some 4],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "add.f32" [r "%r0", r "%r1", .literal "0f3F800000"] =
    .ok (.float
      { op := .add, ty := f32, dsts := [some 0], srcs := [.reg 1, .f32imm 1065353216] }) := rfl
example : Decode.op env "sub.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .sub, ty := f32, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "sub.rz.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .sub, ty := f64, rnd := some .rz, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "sub.rm.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .sub, ty := f32x2, rnd := some .rm, ftz := true, dsts := [some 4],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "mul.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .mul, ty := f32, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "mul.rp.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .mul, ty := f64, rnd := some .rp, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "mul.rz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .mul, ty := f32x2, rnd := some .rz, dsts := [some 4],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "fma.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .fma, ty := f32, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "fma.rz.f64" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    .ok (.float
      { op := .fma, ty := f64, rnd := some .rz, dsts := [some 4],
        srcs := [.reg 5, .reg 6, .reg 7] }) := rfl
example : Decode.op env "fma.rm.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    .ok (.float
      { op := .fma, ty := f32x2, rnd := some .rm, ftz := true, dsts := [some 4],
        srcs := [.reg 5, .reg 6, .reg 7] }) := rfl
example : Decode.op env "mad.rp.ftz.sat.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .mad, ty := f32, rnd := some .rp, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "mad.rn.f64" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    .ok (.float
      { op := .mad, ty := f64, rnd := some .rn, dsts := [some 4],
        srcs := [.reg 5, .reg 6, .reg 7] }) := rfl
example : Decode.op env "div.approx.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .div, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "div.full.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .div, ty := f32, mode := .full, ftz := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "div.full.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .div, ty := f32, mode := .full, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "div.rn.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .div, ty := f64, rnd := some .rn, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "div.rz.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .div, ty := f32, rnd := some .rz, ftz := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "div.rm.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .div, ty := f32, rnd := some .rm, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "div.rp.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .div, ty := f64, rnd := some .rp, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl

/-! ## Unary and approximate operations (§9.7.3.9 to §9.7.3.22) -/

example : Decode.op env "abs.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .abs, ty := f32, ftz := true, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "abs.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .abs, ty := f64, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "neg.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .neg, ty := f32, ftz := true, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "neg.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .neg, ty := f64, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "rcp.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .rcp, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "rcp.approx.ftz.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .rcp, ty := f64, mode := .approx, ftz := true, dsts := [some 4],
        srcs := [.reg 5] }) := rfl
example : Decode.op env "rcp.rn.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .rcp, ty := f64, rnd := some .rn, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "rcp.rz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .rcp, ty := f32, rnd := some .rz, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "rcp.rm.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .rcp, ty := f32, rnd := some .rm, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "rcp.rp.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .rcp, ty := f64, rnd := some .rp, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "sqrt.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .sqrt, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "sqrt.rn.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .sqrt, ty := f64, rnd := some .rn, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "sqrt.rz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .sqrt, ty := f32, rnd := some .rz, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "sqrt.rm.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .sqrt, ty := f32, rnd := some .rm, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "sqrt.rp.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .sqrt, ty := f64, rnd := some .rp, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "rsqrt.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .rsqrt, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "rsqrt.approx.f64" [r "%rd0", r "%rd1"] =
    .ok (.float
      { op := .rsqrt, ty := f64, mode := .approx, dsts := [some 4], srcs := [.reg 5] }) := rfl
example : Decode.op env "ex2.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .ex2, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "sin.approx.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .sin, ty := f32, mode := .approx, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "cos.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .cos, ty := f32, mode := .approx, ftz := true, dsts := [some 0],
        srcs := [.reg 1] }) := rfl
example : Decode.op env "lg2.approx.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .lg2, ty := f32, mode := .approx, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "tanh.approx.f32" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .tanh, ty := f32, mode := .approx, dsts := [some 0], srcs := [.reg 1] }) := rfl

/-! ## testp and copysign (§9.7.3.1, §9.7.3.2) -/

example : Decode.op env "testp.finite.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .finite, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.infinite.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .infinite, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.number.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .number, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.notanumber.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .notanumber, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.normal.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .normal, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.subnormal.f32" [r "%p0", r "%r1"] =
    .ok (.float
      { op := .testp .subnormal, ty := f32, dsts := [some 12], srcs := [.reg 1] }) := rfl
example : Decode.op env "testp.normal.f64" [r "%p1", r "%rd1"] =
    .ok (.float
      { op := .testp .normal, ty := f64, dsts := [some 13], srcs := [.reg 5] }) := rfl
example : Decode.op env "copysign.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .copysign, ty := f32, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "copysign.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .copysign, ty := f64, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl

/-! ## Minimum and maximum (§9.7.3.11, §9.7.3.12, §9.7.4.7, §9.7.4.8) -/

example : Decode.op env "min.ftz.NaN.xorsign.abs.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .min, ty := f32, ftz := true, nanMod := true, xorsign := true, absMod := true,
        dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "max.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .max, ty := f64, dsts := [some 4], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "max.NaN.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .max, ty := f16, nanMod := true, dsts := [some 8], srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "min.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .min, ty := bf16, dsts := [some 8], srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "max.ftz.f16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .max, ty := f16x2, ftz := true, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "min.xorsign.abs.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .min, ty := bf16x2, xorsign := true, absMod := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "min.ftz.NaN.abs.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .min, ty := f32, ftz := true, nanMod := true, absMod := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "max.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .max, ty := f32, dsts := [some 0], srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "max.f32" [r "%r0", r "%r1", .literal "0f00000000"] =
    .ok (.float
      { op := .max, ty := f32, dsts := [some 0], srcs := [.reg 1, .f32imm 0] }) := rfl

/-! ## Comparison and predicate setting (§9.7.7.1, §9.7.7.2, §9.7.8.1, §9.7.8.2) -/

example : Decode.op env "setp.eq.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .eq) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.ne.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .ne) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.lt.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.le.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .le) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.gt.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .gt) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.ge.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .ge) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.equ.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .eq) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.neu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .ne) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.ltu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .lt) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.leu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .le) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.gtu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .gt) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.geu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.unord .ge) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.num.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.num) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.nan.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.nan) none, ty := f32, ftz := true, dsts := [some 12],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.lt.f64" [r "%p0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f64, dsts := [some 12],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "setp.lt.f32" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f32, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2] }) := rfl
-- Either destination of `p|q` may be the sink (§9.7.7.2).
example : Decode.op env "setp.lt.f32" [.pair [r "%p0", .sink], r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f32, dsts := [some 12, none],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.lt.and.f32" [.pair [.sink, r "%p1"], r "%r1", r "%r2", r "%p2"] =
    .ok (.float
      { op := .setp (.ord .lt) (some .and), ty := f32, dsts := [none, some 13],
        srcs := [.reg 1, .reg 2, .reg 14] }) := rfl
example : Decode.op env "setp.gt.and.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .gt) (some .and), ty := f32, dsts := [some 12],
        srcs := [.reg 1, .reg 2, .reg 13] }) := rfl
example : Decode.op env "setp.gt.or.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .gt) (some .or), ty := f32, dsts := [some 12],
        srcs := [.reg 1, .reg 2, .reg 13] }) := rfl
example : Decode.op env "setp.gt.xor.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .gt) (some .xor), ty := f32, dsts := [some 12],
        srcs := [.reg 1, .reg 2, .reg 13] }) := rfl
example : Decode.op env "setp.ge.and.f64" [r "%p0", r "%rd1", r "%rd2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .ge) (some .and), ty := f64, dsts := [some 12],
        srcs := [.reg 5, .reg 6, .reg 13] }) := rfl
example : Decode.op env "setp.gt.or.ftz.f32" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    .ok (.float
      { op := .setp (.ord .gt) (some .or), ty := f32, ftz := true, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2, .reg 14] }) := rfl
example : Decode.op env "set.lt.ftz.u32.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .set (.ord .lt) none (.int .u 32), ty := f32, ftz := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "set.ge.s32.f64" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .set (.ord .ge) none (.int .s 32), ty := f64, dsts := [some 0],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "set.gtu.f32.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .set (.unord .gt) none (.float .f32), ty := f32, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "set.lt.and.f32.f32" [r "%r0", r "%r1", r "%r2", r "%p0"] =
    .ok (.float
      { op := .set (.ord .lt) (some .and) (.float .f32), ty := f32, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 12] }) := rfl
example : Decode.op env "set.ne.or.u32.f64" [r "%r0", r "%rd1", r "%rd2", r "%p0"] =
    .ok (.float
      { op := .set (.ord .ne) (some .or) (.int .u 32), ty := f64, dsts := [some 0],
        srcs := [.reg 5, .reg 6, .reg 12] }) := rfl

/-! ## Half precision (§9.7.4) -/

example : Decode.op env "add.rn.ftz.sat.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .add, ty := f16, rnd := some .rn, ftz := true, sat := true, dsts := [some 8],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "add.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .add, ty := bf16x2, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "sub.rn.ftz.sat.f16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .sub, ty := f16x2, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "sub.rn.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .sub, ty := bf16, rnd := some .rn, dsts := [some 8],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "mul.rn.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .mul, ty := bf16, rnd := some .rn, dsts := [some 8],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "mul.f16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .mul, ty := f16x2, dsts := [some 0], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "fma.rn.ftz.sat.f16x2" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .fma, ty := f16x2, rnd := some .rn, ftz := true, sat := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "fma.rn.ftz.relu.f16" [r "%rs0", r "%rs1", r "%rs2", r "%rs3"] =
    .ok (.float
      { op := .fma, ty := f16, rnd := some .rn, ftz := true, relu := true, dsts := [some 8],
        srcs := [.reg 9, .reg 10, .reg 11] }) := rfl
example : Decode.op env "fma.rn.oob.relu.bf16x2" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.float
      { op := .fma, ty := bf16x2, rnd := some .rn, relu := true, oob := true, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "fma.rn.oob.f16" [r "%rs0", r "%rs1", r "%rs2", r "%rs3"] =
    .ok (.float
      { op := .fma, ty := f16, rnd := some .rn, oob := true, dsts := [some 8],
        srcs := [.reg 9, .reg 10, .reg 11] }) := rfl
example : Decode.op env "neg.ftz.f16" [r "%rs0", r "%rs1"] =
    .ok (.float
      { op := .neg, ty := f16, ftz := true, dsts := [some 8], srcs := [.reg 9] }) := rfl
example : Decode.op env "neg.bf16x2" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .neg, ty := bf16x2, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "abs.ftz.f16x2" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .abs, ty := f16x2, ftz := true, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "abs.bf16" [r "%rs0", r "%rs1"] =
    .ok (.float
      { op := .abs, ty := bf16, dsts := [some 8], srcs := [.reg 9] }) := rfl
example : Decode.op env "tanh.approx.f16" [r "%rs0", r "%rs1"] =
    .ok (.float
      { op := .tanh, ty := f16, mode := .approx, dsts := [some 8], srcs := [.reg 9] }) := rfl
example : Decode.op env "tanh.approx.bf16x2" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .tanh, ty := bf16x2, mode := .approx, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "ex2.approx.f16x2" [r "%r0", r "%r1"] =
    .ok (.float
      { op := .ex2, ty := f16x2, mode := .approx, dsts := [some 0], srcs := [.reg 1] }) := rfl
example : Decode.op env "ex2.approx.ftz.bf16" [r "%rs0", r "%rs1"] =
    .ok (.float
      { op := .ex2, ty := bf16, mode := .approx, ftz := true, dsts := [some 8],
        srcs := [.reg 9] }) := rfl
example : Decode.op env "set.lt.ftz.f16.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .set (.ord .lt) none (.float .f16), ty := f16, ftz := true, dsts := [some 8],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "set.eq.bf16x2.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .set (.ord .eq) none (.packed (.float .bf16) 2), ty := bf16x2, dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "set.lt.u16.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .set (.ord .lt) none (.int .u 16), ty := f16, dsts := [some 8],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "set.lt.f16.u16" [r "%rs0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .set (.ord .lt) none (.float .f16), ty := f16, cmpTy := some (.int .u 16),
        dsts := [some 8], srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "set.lt.f16.s32" [r "%rs0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .set (.ord .lt) none (.float .f16), ty := f16, cmpTy := some (.int .s 32),
        dsts := [some 8], srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "set.lt.and.f16.u16" [r "%rs0", r "%rs1", r "%rs2", r "%p0"] =
    .ok (.float
      { op := .set (.ord .lt) (some .and) (.float .f16), ty := f16, cmpTy := some (.int .u 16),
        dsts := [some 8], srcs := [.reg 9, .reg 10, .reg 12] }) := rfl
example : Decode.op env "set.lt.or.f16x2.f16x2" [r "%r0", r "%r1", r "%r2", r "%p0"] =
    .ok (.float
      { op := .set (.ord .lt) (some .or) (.packed (.float .f16) 2), ty := f16x2, dsts := [some 0],
        srcs := [.reg 1, .reg 2, .reg 12] }) := rfl
example : Decode.op env "set.nan.xor.f16.f16" [r "%rs0", r "%rs1", r "%rs2", r "%p0"] =
    .ok (.float
      { op := .set .nan (some .xor) (.float .f16), ty := f16, dsts := [some 8],
        srcs := [.reg 9, .reg 10, .reg 12] }) := rfl
example : Decode.op env "setp.lt.f16" [r "%p0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f16, dsts := [some 12],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "setp.lt.bf16" [r "%p0", r "%rs1", r "%rs2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := bf16, dsts := [some 12],
        srcs := [.reg 9, .reg 10] }) := rfl
example : Decode.op env "setp.lt.f16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f16x2, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.nan.bf16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    .ok (.float
      { op := .setp .nan none, ty := bf16x2, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "setp.lt.and.f16" [r "%p0", r "%rs1", r "%rs2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .lt) (some .and), ty := f16, dsts := [some 12],
        srcs := [.reg 9, .reg 10, .reg 13] }) := rfl
example : Decode.op env "setp.lt.xor.bf16" [r "%p0", r "%rs1", r "%rs2", r "%p1"] =
    .ok (.float
      { op := .setp (.ord .lt) (some .xor), ty := bf16, dsts := [some 12],
        srcs := [.reg 9, .reg 10, .reg 13] }) := rfl
example : Decode.op env "setp.lt.or.f16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    .ok (.float
      { op := .setp (.ord .lt) (some .or), ty := f16x2, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2, .reg 14] }) := rfl
example : Decode.op env "setp.ge.and.bf16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    .ok (.float
      { op := .setp (.ord .ge) (some .and), ty := bf16x2, dsts := [some 12, some 13],
        srcs := [.reg 1, .reg 2, .reg 14] }) := rfl

/-! ## Mixed precision (§9.7.5) -/

example : Decode.op env "add.f32.f16" [r "%r0", r "%rs0", r "%r1"] =
    .ok (.float
      { op := .add, ty := f32, srcTys := [f16, f32], dsts := [some 0],
        srcs := [.reg 8, .reg 1] }) := rfl
example : Decode.op env "sub.rz.f32.bf16" [r "%r0", r "%rs0", r "%r1"] =
    .ok (.float
      { op := .sub, ty := f32, srcTys := [bf16, f32], rnd := some .rz, dsts := [some 0],
        srcs := [.reg 8, .reg 1] }) := rfl
example : Decode.op env "add.rn.sat.f32.f16" [r "%r0", r "%rs0", r "%r1"] =
    .ok (.float
      { op := .add, ty := f32, srcTys := [f16, f32], rnd := some .rn, sat := true, dsts := [some 0],
        srcs := [.reg 8, .reg 1] }) := rfl
example : Decode.op env "fma.rn.f32.bf16" [r "%r0", r "%rs0", r "%rs1", r "%r1"] =
    .ok (.float
      { op := .fma, ty := f32, srcTys := [bf16, bf16, f32], rnd := some .rn, dsts := [some 0],
        srcs := [.reg 8, .reg 9, .reg 1] }) := rfl
example : Decode.op env "fma.rm.sat.f32.f16" [r "%r0", r "%rs0", r "%rs1", r "%r1"] =
    .ok (.float
      { op := .fma, ty := f32, srcTys := [f16, f16, f32], rnd := some .rm, sat := true,
        dsts := [some 0], srcs := [.reg 8, .reg 9, .reg 1] }) := rfl
example : Decode.op env "add.rn.f32x2.f16x2.f32x2" [r "%rd0", r "%r1", r "%rd1"] =
    .ok (.float
      { op := .add, ty := f32x2, srcTys := [f16x2, f32x2], rnd := some .rn, dsts := [some 4],
        srcs := [.reg 1, .reg 5] }) := rfl
example : Decode.op env "sub.f32x2.bf16x2.f32x2" [r "%rd0", r "%r1", r "%rd1"] =
    .ok (.float
      { op := .sub, ty := f32x2, srcTys := [bf16x2, f32x2], dsts := [some 4],
        srcs := [.reg 1, .reg 5] }) := rfl
example : Decode.op env "add.rz.ftz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .add, ty := f16x2, srcTys := [f32x2, f32x2], rnd := some .rz, ftz := true,
        dsts := [some 0], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "sub.rz.ftz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .sub, ty := f16x2, srcTys := [f32x2, f32x2], rnd := some .rz, ftz := true,
        dsts := [some 0], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "add.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .add, ty := bf16x2, srcTys := [f32x2, f32x2], rnd := some .rz, dsts := [some 0],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "sub.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .sub, ty := bf16x2, srcTys := [f32x2, f32x2], rnd := some .rz, dsts := [some 0],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "mul.ftz.rz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .mul, ty := f16x2, srcTys := [f32x2, f32x2], rnd := some .rz, ftz := true,
        dsts := [some 0], srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "mul.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .mul, ty := bf16x2, srcTys := [f32x2, f32x2], rnd := some .rz, dsts := [some 0],
        srcs := [.reg 5, .reg 6] }) := rfl
example : Decode.op env "fma.rn.f32x2.f16x2.f32x2.f32x2" [r "%rd0", r "%r1", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .fma, ty := f32x2, srcTys := [f16x2, f32x2, f32x2], rnd := some .rn, dsts := [some 4],
        srcs := [.reg 1, .reg 5, .reg 6] }) := rfl
example : Decode.op env "fma.rp.f32x2.bf16x2.f32x2.f32x2" [r "%rd0", r "%r1", r "%rd1", r "%rd2"] =
    .ok (.float
      { op := .fma, ty := f32x2, srcTys := [bf16x2, f32x2, f32x2], rnd := some .rp,
        dsts := [some 4], srcs := [.reg 1, .reg 5, .reg 6] }) := rfl
example : Decode.op env "mul.bf16x2.bf16x2.f16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .mul, ty := bf16x2, srcTys := [bf16x2, f16x2], dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl
example : Decode.op env "mul.f16x2.f16x2.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .mul, ty := f16x2, srcTys := [f16x2, bf16x2], dsts := [some 0],
        srcs := [.reg 1, .reg 2] }) := rfl

/-! ## Rules (FloatInstr.rule, design section 13) -/

-- Every decoded form has THREAD-FLOAT, except `div.full`, the mixed `fma` with a packed half
-- `.atype` and the `mul` forms that mix `.f16x2` and `.bf16x2`.
example : rule "add.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "add.rm.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "add.rp.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "add.f32" [r "%r0", r "%r1", .literal "0f3F800000"] =
    some (some .threadFloat) := rfl
example : rule "sub.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rz.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rm.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "mul.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "mul.rp.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "mul.rz.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.ftz.sat.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "fma.rz.f64" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    some (some .threadFloat) := rfl
example : rule "fma.rm.ftz.f32x2" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    some (some .threadFloat) := rfl
example : rule "mad.rp.ftz.sat.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "mad.rn.f64" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    some (some .threadFloat) := rfl
example : rule "div.approx.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "div.full.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    some none := rfl
example : rule "div.full.f32" [r "%r0", r "%r1", r "%r2"] =
    some none := rfl
example : rule "div.rn.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "div.rz.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "div.rm.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "div.rp.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "abs.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "abs.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "neg.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "neg.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.approx.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.approx.ftz.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.rn.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.rz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.rm.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "rcp.rp.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "sqrt.approx.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "sqrt.rn.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "sqrt.rz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "sqrt.rm.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "sqrt.rp.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "rsqrt.approx.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "rsqrt.approx.f64" [r "%rd0", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "ex2.approx.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "sin.approx.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "cos.approx.ftz.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "lg2.approx.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "tanh.approx.f32" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.finite.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.infinite.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.number.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.notanumber.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.normal.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.subnormal.f32" [r "%p0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "testp.normal.f64" [r "%p1", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "copysign.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "copysign.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "min.ftz.NaN.xorsign.abs.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "max.f64" [r "%rd0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "max.NaN.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "min.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "max.ftz.f16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "min.xorsign.abs.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "min.ftz.NaN.abs.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "max.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "max.f32" [r "%r0", r "%r1", .literal "0f00000000"] =
    some (some .threadFloat) := rfl
example : rule "setp.eq.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.ne.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.le.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.gt.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.ge.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.equ.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.neu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.ltu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.leu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.gtu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.geu.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.num.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.nan.ftz.f32" [r "%p0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.f64" [r "%p0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.f32" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.gt.and.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.gt.or.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.gt.xor.f32" [r "%p0", r "%r1", r "%r2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.ge.and.f64" [r "%p0", r "%rd1", r "%rd2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.gt.or.ftz.f32" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.ftz.u32.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "set.ge.s32.f64" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "set.gtu.f32.f32" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.and.f32.f32" [r "%r0", r "%r1", r "%r2", r "%p0"] =
    some (some .threadFloat) := rfl
example : rule "set.ne.or.u32.f64" [r "%r0", r "%rd1", r "%rd2", r "%p0"] =
    some (some .threadFloat) := rfl
example : rule "add.rn.ftz.sat.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "add.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rn.ftz.sat.f16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rn.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "mul.rn.bf16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "mul.f16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.ftz.sat.f16x2" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.ftz.relu.f16" [r "%rs0", r "%rs1", r "%rs2", r "%rs3"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.oob.relu.bf16x2" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.oob.f16" [r "%rs0", r "%rs1", r "%rs2", r "%rs3"] =
    some (some .threadFloat) := rfl
example : rule "neg.ftz.f16" [r "%rs0", r "%rs1"] =
    some (some .threadFloat) := rfl
example : rule "neg.bf16x2" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "abs.ftz.f16x2" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "abs.bf16" [r "%rs0", r "%rs1"] =
    some (some .threadFloat) := rfl
example : rule "tanh.approx.f16" [r "%rs0", r "%rs1"] =
    some (some .threadFloat) := rfl
example : rule "tanh.approx.bf16x2" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "ex2.approx.f16x2" [r "%r0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "ex2.approx.ftz.bf16" [r "%rs0", r "%rs1"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.ftz.f16.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "set.eq.bf16x2.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.u16.f16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.f16.u16" [r "%rs0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.f16.s32" [r "%rs0", r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.and.f16.u16" [r "%rs0", r "%rs1", r "%rs2", r "%p0"] =
    some (some .threadFloat) := rfl
example : rule "set.lt.or.f16x2.f16x2" [r "%r0", r "%r1", r "%r2", r "%p0"] =
    some (some .threadFloat) := rfl
example : rule "set.nan.xor.f16.f16" [r "%rs0", r "%rs1", r "%rs2", r "%p0"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.f16" [r "%p0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.bf16" [r "%p0", r "%rs1", r "%rs2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.f16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.nan.bf16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.and.f16" [r "%p0", r "%rs1", r "%rs2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.xor.bf16" [r "%p0", r "%rs1", r "%rs2", r "%p1"] =
    some (some .threadFloat) := rfl
example : rule "setp.lt.or.f16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    some (some .threadFloat) := rfl
example : rule "setp.ge.and.bf16x2" [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", r "%p2"] =
    some (some .threadFloat) := rfl
example : rule "add.f32.f16" [r "%r0", r "%rs0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "sub.rz.f32.bf16" [r "%r0", r "%rs0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "add.rn.sat.f32.f16" [r "%r0", r "%rs0", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.f32.bf16" [r "%r0", r "%rs0", r "%rs1", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "fma.rm.sat.f32.f16" [r "%r0", r "%rs0", r "%rs1", r "%r1"] =
    some (some .threadFloat) := rfl
example : rule "add.rn.f32x2.f16x2.f32x2" [r "%rd0", r "%r1", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "sub.f32x2.bf16x2.f32x2" [r "%rd0", r "%r1", r "%rd1"] =
    some (some .threadFloat) := rfl
example : rule "add.rz.ftz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rz.ftz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "add.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "sub.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "mul.ftz.rz.f16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "mul.rz.bf16x2.f32x2.f32x2" [r "%r0", r "%rd1", r "%rd2"] =
    some (some .threadFloat) := rfl
example : rule "fma.rn.f32x2.f16x2.f32x2.f32x2" [r "%rd0", r "%r1", r "%rd1", r "%rd2"] =
    some none := rfl
example : rule "fma.rp.f32x2.bf16x2.f32x2.f32x2" [r "%rd0", r "%r1", r "%rd1", r "%rd2"] =
    some none := rfl
example : rule "mul.bf16x2.bf16x2.f16x2" [r "%r0", r "%r1", r "%r2"] =
    some none := rfl
example : rule "mul.f16x2.f16x2.bf16x2" [r "%r0", r "%r1", r "%r2"] =
    some none := rfl

/-! ## Operand widths and constants -/

-- A `.f32x2` operand is a 64-bit register, `.f16x2` and `.bf16x2` a 32-bit register, scalar
-- `.f16` and `.bf16` a 16-bit register.
example : (Decode.op env "add.rn.f32x2" [r "%rd0", r "%rd1", r "%rd2"]).isOk = true := rfl
example : (Decode.op env "add.rn.f32x2" [r "%r0", r "%rd1", r "%rd2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32x2" [r "%rd0", r "%rd1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f16x2" [r "%r0", r "%r1", r "%r2"]).isOk = true := rfl
example : (Decode.op env "add.rn.f16x2" [r "%rd0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "add.rn.bf16x2" [r "%r0", r "%rd1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f16" [r "%rs0", r "%rs1", r "%rs2"]).isOk = true := rfl
example : (Decode.op env "add.rn.f16" [r "%r0", r "%rs1", r "%rs2"]).isOk = false := rfl
example : (Decode.op env "mul.rn.bf16" [r "%rs0", r "%rs1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32" [r "%rd0", r "%rd1", r "%rd2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f64" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
-- The result of `testp` and `setp` is a predicate register; a mixed form checks each source at
-- its own width.
example : (Decode.op env "testp.finite.f32" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32.f16" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32x2.f16x2.f32x2" [r "%rd0", r "%rd1", r "%rd2"]).isOk = false :=
  rfl
-- A `0f` constant is accepted for an `.f32` operand and for nothing wider.
example : Decode.op env "add.rn.f32" [r "%r0", r "%r1", .literal "0f3F800000"] =
    .ok (.float
      { op := .add, ty := f32, rnd := some .rn, dsts := [some 0],
        srcs := [.reg 1, .f32imm 0x3F800000] }) := rfl
example : Decode.op env "setp.lt.f32" [r "%p0", .literal "0fFF800000", r "%r2"] =
    .ok (.float
      { op := .setp (.ord .lt) none, ty := f32, dsts := [some 12],
        srcs := [.f32imm 0xFF800000, .reg 2] }) := rfl
example : (Decode.op env "add.rn.f64" [r "%rd0", r "%rd1", .literal "0f3F800000"]).isOk = false :=
  rfl

/-! ## Rejected forms -/

-- A negated predicate source `!c` (`Syntax.Operand.negate`) does not decode.
example : (Decode.op env "setp.lt.and.f32"
    [r "%p0", r "%r1", r "%r2", .negate (r "%p1")]).isOk = false := rfl
example : (Decode.op env "set.lt.and.f32.f32"
    [r "%r0", r "%r1", r "%r2", .negate (r "%p1")]).isOk = false := rfl
example : (Decode.op env "setp.lt.or.f16x2"
    [.pair [r "%p0", r "%p1"], r "%r1", r "%r2", .negate (r "%p2")]).isOk = false := rfl
-- `lo`, `ls`, `hi` and `hs` are integer comparisons.
example : (Decode.op env "setp.lo.f32" [r "%p0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "setp.ls.f32" [r "%p0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "setp.hi.f32" [r "%p0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "setp.hs.f64" [r "%p0", r "%rd1", r "%rd2"]).isOk = false := rfl
example : (Decode.op env "set.lo.u32.f32" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
-- `.relu` on a floating `min` or `max` is not defined.
example : (Decode.op env "max.relu.f32" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "min.relu.f16x2" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "max.relu.f32" [r "%r0", r "%r1", r "%r2", r "%r3"]).isOk = false := rfl
-- A `0d` constant and a decimal floating literal do not decode (`Opnd` holds `0f` constants).
example : (Decode.op env "add.rn.f64" [r "%rd0", r "%rd1", .literal "0d3FF0000000000000"]).isOk =
    false := rfl
example : (Decode.op env "add.rn.f32" [r "%r0", r "%r1", .literal "0d3FF0000000000000"]).isOk =
    false := rfl
example : (Decode.op env "add.rn.f32" [r "%r0", r "%r1", .literal "1.5"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32" [r "%r0", r "%r1", .literal "1.0e0"]).isOk = false := rfl
-- `.2pi` is not an opcode token of `sin`.
example : (Decode.op env "sin.approx.2pi.f32" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "sin.approx.f32.2pi" [r "%r0", r "%r1"]).isOk = false := rfl
-- An integer constant at a floating type (Table 26).
example : (Decode.op env "add.rn.f32" [r "%r0", r "%r1", .literal "1"]).isOk = false := rfl
example : (Decode.op env "max.f32" [r "%r0", r "%r1", .literal "0"]).isOk = false := rfl
example : (Decode.op env "setp.lt.f32" [r "%p0", r "%r1", .literal "3"]).isOk = false := rfl
-- `fma` and `mad` need a rounding modifier (§9.7.3.6: "fma.rnd"); so does `fma` with a packed
-- vector.
example : (Decode.op env "fma.f32" [r "%r0", r "%r1", r "%r2", r "%r3"]).isOk = false := rfl
example : (Decode.op env "fma.f64" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"]).isOk = false := rfl
example : (Decode.op env "mad.f32" [r "%r0", r "%r1", r "%r2", r "%r3"]).isOk = false := rfl
example : (Decode.op env "fma.f32x2" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"]).isOk = false := rfl
-- Both destinations of `setp` cannot be the sink.
example : (Decode.op env "setp.lt.f32" [.pair [.sink, .sink], r "%r1", r "%r2"]).isOk = false :=
  rfl
-- A `.f64` form of an approximate operation the manual does not define, and an operand count
-- outside the syntax.
example : (Decode.op env "sin.approx.f64" [r "%rd0", r "%rd1"]).isOk = false := rfl
example : (Decode.op env "div.approx.f64" [r "%rd0", r "%rd1", r "%rd2"]).isOk = false := rfl
example : (Decode.op env "add.rn.f32" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "min.f32" [r "%r0", r "%r1", r "%r2", r "%r3", r "%r0"]).isOk = false :=
  rfl

end

end PTX.Tests.FloatDecode
