-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Float.FloatIeee
public import Core.Source.Decode
public import Core.Thread.Local
public import Core.Thread.Access

/-! Floating instructions through `execLocal` (THREAD-FLOAT, `execFloat`): `setp` with `p|q` and
`BoolOp`, the `set` encodings and the pairs of `Semantics` and `Description` that conflict, the
opaque NaN, and `add`, `sub` with and without a rounding modifier. -/
namespace PTX.Tests.FloatExec
noncomputable section

private def launch : Launch := { grid := 1, block := 1, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%p".toList, 4, 1⟩], labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %p0..%p3 = 4..7
private def r (n : String) : Syntax.Operand := .register n

@[expose] public section

/-- The format of `.f32` and `.f16x2` in the examples. -/
def f32 : FTy := { fmt := .f32 }
def f16x2 : FTy := { fmt := .f16, lanes := 2 }

/-- Evaluate an instruction through `execLocal`: unfold the dispatch, the operand reads, the lane
rule and the encodings, then normalize. -/
macro "exec_eval" : tactic => `(tactic| (
  simp (config := { decide := true }) [execLocal, Op.rule, execFloat, boolCombine, readPred,
    readValue, readReg, setReg, setDst, classify, floatLane, splitValue, unitValue, setResult,
    FVal.toValue, Value.bitPattern, Value.bytes, FloatFmt.bytes, Layout.signPattern,
    Layout.infPattern, BoolOp.eval, Function.update_self, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw, FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee,
    FloatInstr.arith, FloatInstr.compare, FloatInstr.approx, FloatInstr.approxTable?,
    FloatInstr.flushIn, FloatInstr.srcFmt, FVal.add, FVal.mul, FVal.div, FVal.toRat, FVal.isNeg,
    FVal.isNaN, FVal.negate, FVal.absV, FVal.sat, FVal.relu, FVal.lt, FVal.minMax, minMaxOp,
    FVal.copysign, FVal.signBit, FVal.withSign, FVal.subnormalIn, Cmp.evalF, FCmp.eval,
    TestProp.eval, Layout.roundVal, Layout.sqrt, Layout.flush, Layout.subnormal,
    Layout.minNormal, Layout.bias, Layout.width, FloatFmt.layout, FloatRound.mode, ACls.of,
    ARes.val, divApprox, approxF64, upperWord, upperLayout, Layout.decode, Layout.magnitude,
    Layout.fieldVal, Layout.topField, rcpTable, rcpF64Table, sqrtTable, rsqrtTable,
    rsqrtF64Table, sinTable, cosTable, lg2Table, ex2Table, tanhTable, ex2Bf16Table, ex2F16Table,
    List.lookup, Tests.FloatIeee.acls_beq, f32, f16x2, Except.map, List.map, next, truncBits,
    readBits, compare, intOf, toSigned, BitVec.toNat_ofNat, List.range_succ, List.mapM_cons,
    List.mapM_nil, List.range_zero, List.append_nil, Function.update_apply]
  <;> norm_num))

end

/-- A thread state holding the given registers. -/
private def mk : List (Nat × Value) → TState
  | [] => {}
  | (r, v) :: rest => setReg (mk rest) r v

/-- The values of registers `rs` after executing `op` in the state `mk rs0`. -/
private def run (rs0 : List (Nat × Value)) (op : Op) (rs : List Nat) : Exec (List (Exec Value)) :=
  (execLocal launch 0 (mk rs0) op).map fun t => rs.map (readReg t)

/-- The outcome that gives registers the values `vs`. -/
local notation "got" vs:max => (Except.ok (List.map Except.ok vs) : Exec (List (Exec Value)))

private def fi (op : FOp) (ty : FTy) (dsts : List (Option Nat)) (srcs : List Opnd)
    (rnd : Option FloatRound := none) (mode : FMode := .ieee) : Op :=
  .float { op, ty, rnd, mode, dsts, srcs }

local notation "one" => (Value.bits 32 0x3f800000)
local notation "two" => (Value.bits 32 0x40000000)
local notation "isT" => (Value.pred true)
local notation "isF" => (Value.pred false)

/-! ## `setp` with `p|q` and `BoolOp` -/

/-- `setp.lt.and.f32 %p0|%p1, %r0, %r1, %p2` -/
private def setpLtAnd : Op :=
  fi (.setp (.ord .lt) (some .and)) f32 [some 4, some 5] [.reg 0, .reg 1, .reg 6]

private def abc (x y : Value) (c : Bool) : List (Nat × Value) := [(0, x), (1, y), (6, .pred c)]

/-- `setp.lt.f16x2 %p0|%p1, %r0, %r1` -/
private def setpLtX2 : Op := fi (.setp (.ord .lt) none) f16x2 [some 4, some 5] [.reg 0, .reg 1]

/-- `setp.lt.f32 %p0|_, %r1, %r2` -/
private def setpSink : Op := fi (.setp (.ord .lt) none) f32 [some 4, none] [.reg 1, .reg 2]

-- `p = BoolOp(t, c)` and `q = BoolOp(!t, c)` with `.and`: the four cases of `t` and `c`. The packed
-- form gives `p` and `q` the two lanes (halves `0x3c00` is 1.0, `0x4000` is 2.0, `0x4200` is 3.0),
-- and with the sink `_` only `p` is written.
example :
    (run (abc one two true) setpLtAnd [4, 5] = got [isT, isF]) ∧
    (run (abc two one true) setpLtAnd [4, 5] = got [isF, isT]) ∧
    (run (abc one two false) setpLtAnd [4, 5] = got [isF, isF]) ∧
    (run (abc two one false) setpLtAnd [4, 5] = got [isF, isF]) ∧
    (run [(0, .bits 32 0x3c003c00), (1, .bits 32 0x40004000)] setpLtX2 [4, 5] = got [isT, isT]) ∧
    (run [(0, .bits 32 0x42003c00), (1, .bits 32 0x40004000)] setpLtX2 [4, 5] = got [isT, isF]) ∧
    (run [(1, one), (2, two)] setpSink [4, 5] = .ok [.ok isT, .error .uninitialized]) := by
  simp only [run, mk, setpLtAnd, setpLtX2, setpSink, fi, abc]; exec_eval

-- `setp.lt.f32 %p0|_, %r1, %r2` decodes with the sink.
example : Decode.op env "setp.lt.f32" [.pair [r "%p0", .sink], r "%r1", r "%r2"] = .ok setpSink :=
  rfl

/-! ## `set` encodings (§9.7.8.1, §9.7.7.1) -/

private def setI (dst : DType) (ty : FTy) (srcs : List Opnd := [.reg 1, .reg 2])
    (cmpTy : Option DType := none) : Op :=
  .float { op := .set (.ord .lt) none dst, ty, cmpTy, dsts := [some 0], srcs }

example : Decode.op env "set.lt.f32.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (setI (.float .f32) f32) := rfl
example : Decode.op env "set.lt.u32.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (setI (.int .u 32) f32) := rfl

private def lt12 : List (Nat × Value) := [(1, one), (2, two)]
private def gt12 : List (Nat × Value) := [(1, two), (2, one)]
private def halves (a b : Nat) : List (Nat × Value) := [(1, .bits 32 a), (2, .bits 32 b)]
private def s32 : Option DType := some (.int .s 32)

-- `set.lt.f32.f32` writes the payload `1.0` or `0.0`; `set.lt.u32.f32` all ones or zero;
-- `set.lt.f16.f32` writes `1.0` in `.f16`; `set.lt.u32.f16x2` packs `0xffff` or `0` per half, low
-- lane first; `set.lt.f16.s32` compares integers (`-1 < 1` is true as `.s32`, false as `.u32`).
example :
    (run lt12 (setI (.float .f32) f32) [0] = got [.float .f32 1]) ∧
    (run gt12 (setI (.float .f32) f32) [0] = got [.float .f32 0]) ∧
    (run lt12 (setI (.int .u 32) f32) [0] = got [.bits 32 0xffffffff]) ∧
    (run gt12 (setI (.int .u 32) f32) [0] = got [.bits 32 0]) ∧
    (run lt12 (setI (.float .f16) f32) [0] = got [.float .f16 1]) ∧
    (run (halves 0x42003c00 0x40004000) (setI (.int .u 32) f16x2) [0] = got [.bits 32 0xffff]) ∧
    (run (halves 0x3c003c00 0x40004000) (setI (.int .u 32) f16x2) [0] =
      got [.bits 32 0xffffffff]) ∧
    (run (halves 0xffffffff 1) (setI (.float .f16) ⟨.f16, 1⟩ [.reg 1, .reg 2] s32) [0] =
      got [.float .f16 1]) ∧
    (run (halves 0xffffffff 1) (setI (.float .f16) ⟨.f16, 1⟩ [.reg 1, .reg 2] (some (.int .u 32)))
      [0] = got [.float .f16 0]) := by
  simp only [run, mk, setI, lt12, gt12, halves, s32]; exec_eval

-- The Semantics and the Description of §9.7.8.1 disagree on `.bf16`: no rule.
example :
    (execLocal launch 0 (mk lt12) (setI (.float .bf16) f32) = .error .noRule) ∧
    (execLocal launch 0 (mk [(1, .bits 16 0x3f80), (2, .bits 16 0x4000)])
      (setI (.int .u 32) ⟨.bf16, 1⟩) = .error .noRule) := by
  simp only [mk, setI, lt12]; exec_eval

/-! ## The opaque NaN -/

-- An `add.rn.f32` with a NaN operand, as bits or as the opaque NaN, writes the opaque NaN;
-- `setp.eq.f32` with it is false and `setp.equ.f32` true.
example :
    (run (halves 0x7fc00000 0x3f800000) (fi .add f32 [some 0] [.reg 1, .reg 2] (some .rn)) [0] =
      got [.nan .f32]) ∧
    (run [(1, .nan .f32), (2, one)] (fi .add f32 [some 0] [.reg 1, .reg 2] (some .rn)) [0] =
      got [.nan .f32]) ∧
    (run [(1, .nan .f32), (2, one)] (fi (.setp (.ord .eq) none) f32 [some 4] [.reg 1, .reg 2])
      [4] = got [isF]) ∧
    (run [(1, .nan .f32), (2, one)] (fi (.setp (.unord .eq) none) f32 [some 4] [.reg 1, .reg 2])
      [4] = got [isT]) := by
  simp only [run, mk, fi, halves]; exec_eval
-- An integer instruction cannot read it.
example : execLocal launch 0 (mk [(0, .nan .f32)])
    (.int ⟨.and, .int .b 32, false, [some 1], [.reg 0, .imm 0x80000000]⟩) =
    .error .typeMismatch := by
  rfl
-- Its bytes rebuild it.
example : rebuild 3 ((Value.nan .f32).toBytes.map some) = .ok (.nan .f32) := by
  have h : (Value.nan .f32).toBytes.map some = [some (.nan .f32, 0), some (.nan .f32, 1),
      some (.nan .f32, 2), some (.nan .f32, 3)] := by
    simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ, Value.byteAt]
  rw [h]
  show rebuild (Nat.succ 2) (some (Value.nan .f32, 0) :: _) = _
  rw [rebuild.eq_2]
  simp [Value.bytes, FloatFmt.bytes, h, pure, Except.pure]

/-! ## `add` and `sub` with and without a rounding modifier -/

-- Without a written modifier `add` has no Core result; `x - x` is `+0` under `.rn` and `-0`,
-- written as its bits, under `.rm`.
example :
    (execLocal launch 0 (mk lt12) (fi .add f32 [some 0] [.reg 1, .reg 2]) = .error .noRule) ∧
    (run (halves 0x3f800000 0x3f800000) (fi .sub f32 [some 0] [.reg 1, .reg 2] (some .rm)) [0] =
      got [.bits 32 0x80000000]) ∧
    (run (halves 0x3f800000 0x3f800000) (fi .sub f32 [some 0] [.reg 1, .reg 2] (some .rn)) [0] =
      got [.float .f32 0]) ∧
    (execLocal launch 0 (mk lt12) (fi .sub f32 [some 0] [.reg 1, .reg 2]) = .error .noRule) ∧
    (run (halves 0x80000000 0x80000000) (fi .add f32 [some 0] [.reg 1, .reg 2] (some .rn)) [0] =
      got [.bits 32 0x80000000]) := by
  simp only [run, mk, fi, lt12, halves]; exec_eval

-- `1.0 + 2.0` under `.rm` is exact: `3.0` is the field `0x40400000` of `.f32`.
private theorem roundFtz_false (L : Layout) (m : RoundMode) (r : ℝ) :
    L.roundFtz m false r = L.round m .inf r false := by
  simp [Layout.roundFtz]
example : run lt12 (fi .add f32 [some 0] [.reg 1, .reg 2] (some .rm)) [0] =
    got [.float .f32 3] := by
  simp only [run, mk, fi, lt12]; exec_eval
  rw [roundFtz_false, Layout.round_exact (eb := 8) (mb := 23) (m := .rm) (x := 3)
    (F := 0x40400000) trivial (by norm_num) (by decide)
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]

/-! ## What Core gives the forms that no assumption scope covers

The forms that `idealReal` and `approxExact` leave to the Core rule (Tests/Float/FloatForms.lean):
directed rounding, `setp` with an infinite operand, the approximations on an infinite operand
and at 0, and `cvt.f32.f16` of `-0`. -/

private def pair (a b : Nat) : Value := .bits 64 (BitVec.ofNat 64 (a + 2 ^ 32 * b))

example :
    -- `add.rm.f32x2` of `(1, -1)` and `(-1, 1)`: `-0` in each lane (`0xbf800000` is `-1.0`).
    (run [(5, pair 0x3f800000 0xbf800000), (6, pair 0xbf800000 0x3f800000)]
      (fi .add ⟨.f32, 2⟩ [some 4] [.reg 5, .reg 6] (some .rm)) [4] =
      got [.pair (.bits 32 0x80000000) (.bits 32 0x80000000)]) ∧
    -- `sub.rn.f32x2` of `(1, 1)` and `(1, 1)`: `+0` in each lane.
    (run [(5, pair 0x3f800000 0x3f800000), (6, pair 0x3f800000 0x3f800000)]
      (fi .sub ⟨.f32, 2⟩ [some 4] [.reg 5, .reg 6] (some .rn)) [4] =
      got [.pair (.float .f32 0) (.float .f32 0)]) ∧
    -- `sub.rz.f32` of `1` and `1` is `+0`.
    (run lt12 (fi .sub f32 [some 0] [.reg 1, .reg 1] (some .rz)) [0] = got [.float .f32 0]) ∧
    -- `ex2.approx.f32` of `-inf` (`0xff800000`) is `+0`; `rcp.approx.f32` of `+0` is `+inf`.
    (run [(1, .bits 32 0xff800000)] (fi .ex2 f32 [some 0] [.reg 1] none .approx) [0] =
      got [.float .f32 0]) ∧
    (run [(1, .bits 32 0)] (fi .rcp f32 [some 0] [.reg 1] none .approx) [0] =
      got [.bits 32 0x7f800000]) ∧
    -- `setp.neu.f32 %p0, %r1, 0fFF800000` with `%r1 = 1.0`, and `setp.lt.f32` with a register
    -- that holds `-inf`.
    (run lt12 (fi (.setp (.unord .ne) none) f32 [some 4] [.reg 1, .f32imm 0xFF800000]) [4] =
      got [isT]) ∧
    (run [(1, .bits 32 0xff800000), (2, one)] (fi (.setp (.ord .lt) none) f32 [some 4]
      [.reg 1, .reg 2]) [4] = got [isT]) := by
  simp only [run, mk, fi, lt12, pair]; exec_eval

/-- `cvt.f32.f16 %r0, %r1` -/
private def cvtWiden : CvtInstr :=
  { dst := .float .f32, src := .float .f16, d := 0, srcs := [.reg 1] }

private theorem goCvt {c : CvtInstr} {t : TState} (h : c.rule = some .threadCvt) :
    execLocal launch 0 t (.cvt c) = execCvt launch 0 t c := by
  simp only [execLocal, Op.rule, h]

-- `cvt.f32.f16` of the pattern `0x8000` (`-0`) writes the bits of `-0`.
example : execLocal launch 0 (mk [(1, .bits 16 0x8000)]) (.cvt cvtWiden) =
    .ok (next (setReg (mk [(1, .bits 16 0x8000)]) 0 (.bits 32 0x80000000))) := by
  rw [goCvt rfl]
  simp only [cvtWiden, mk]
  dsimp only [execCvt, FType.fmt?]
  norm_num [readCvtFloat, lowValue, lowBitsValue, readReg, readValue, readBits, setReg,
    Function.update_self, classify, Value.bitPattern, Value.bytes, FloatFmt.bytes,
    FloatFmt.layout, FType.layout?, Layout.decode, Layout.width, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal, Layout.minNormal,
    Layout.maxNorm, Layout.topField, FVal.toValue, Layout.signPattern, Layout.infPattern,
    cvtFloatDst, CvtRnd.roundInt, CvtRnd.mode?, cvtIntOf, FVal.sat, reluFVal, pzoFVal,
    cvtFinish, widenElem, roundIntElem, cvtElem, packedElems, splitValue, FType.fmt?,
    cvtScales, cvtPack, cvtSpecial, cvtNum, cvtRound, satMaxNorm, FVal.ofRat, truncBits, intOf,
    toSigned,
    intSat, intBits, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]
  try rfl

end
end PTX.Tests.FloatExec
