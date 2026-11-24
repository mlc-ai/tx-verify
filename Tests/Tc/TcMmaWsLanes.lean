-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup
public import Core.Tc.TcMmaSafety
public import Assumption.IdealReal

/-! `.ws` with M < 128 reads one A row per D lane (EXT-TCFIG), checked on a B200 by
`Tools/probes/tcgen05_ws_ts_i8.ptx` (A in Tensor Memory, N = 64, decoys in every other lane). -/
namespace PTX.Tests.TcMmaWsLanes
open TcMma Assumption
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 40, 32⟩, ⟨"rd".toList, 10, 64⟩, ⟨"p".toList, 5, 1⟩], labels := [],
      params := [] }

/-! ## Decoding: the probe's instruction and the `[a-tmem]` `.ws` forms -/

example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::i8"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"] =
    .ok (.tcMma <| .dense .one true .i8 8 (.tmem 39 0) (.reg 48) (.reg 13)
      (List.replicate 4 (.imm 0)) (.reg 54)) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::i8.collector::b0::discard"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"] =
    .ok (.tcMma <| .dense .one true .i8 8 (.tmem 39 0) (.reg 48) (.reg 13)
      (List.replicate 4 (.imm 0)) (.reg 54)) := rfl
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::f16"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"] =
    .ok (.tcMma <| .dense .one true .f16 8 (.tmem 39 0) (.reg 48) (.reg 13)
      (List.replicate 4 (.imm 0)) (.reg 54)) := rfl
-- Kinds without a representation decode to an instruction with no rule; the `.sp` forms are
-- rejected.
private def noRule : Except String Op → Bool
  | .ok op => op.rule.isNone
  | _ => false
example : Decode.op env "tcgen05.mma.ws.cta_group::1.kind::tf32"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"] =
    .ok (.tcMma <| .dense .one true .tf32 8 (.tmem 39 0) (.reg 48) (.reg 13)
      (List.replicate 4 (.imm 0)) (.reg 54)) := rfl
example : noRule (Decode.op env "tcgen05.mma.ws.cta_group::1.kind::ti16"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"]) = true := rfl
example : noRule (Decode.op env "tcgen05.mma.ws.cta_group::1.kind::ti16.collector::b0::lastuse"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8", .register "r13",
      .register "p4"]) = true := rfl
example (L : Launch) (g : Nat) (t : TState) (r : Isa.Raw) :
    eventTmpl [] L g t (.unmodeled r) = .ub .noRule := rfl
example : (Decode.op env "tcgen05.mma.ws.sp.cta_group::1.kind::i8"
    [.address [.register "r8"], .address [.register "r39"], .register "rd8",
      .address [.register "r33"], .register "r13", .register "p4"]).isOk = false := rfl
example : (Decode.op env "tcgen05.mma.sp.cta_group::1.kind::i8"
    [.address [.register "r8"], .register "rd6", .register "rd8", .address [.register "r33"],
      .register "r13", .vector (List.replicate 4 (.register "r24")), .register "p4"]).isOk =
    false := rfl
example :
    (Op.tcMma <| .dense .one true .i8 8 (.tmem 39 0) (.reg 48) (.reg 13) [] (.reg 54)).tcGroup =
      some 1 := rfl

/-! ## The probe's descriptors (IDESC in `run_tcgen05_ws_ts_i8.cu`) -/

private def wsDesc (m : Nat) : Descriptor :=
  ⟨.one, .i8 true true false, m, 64, false, false, false, false, true⟩
example : decode .one true .i8 68158624 = some (wsDesc 64) := by decide
example : decode .one true .i8 34604192 = some (wsDesc 32) := by decide
example : decode .one true .i8 135267488 = some (wsDesc 128) := by decide
-- The former sparse flag (bit 2) has no represented meaning.
example : decode .one true .i8 (68158624 + 4) = none := by decide
example : decode .one false .i8 (134349984 + 4) = none := by decide

/-! ## Operand rows: 128 lane rows for A with `.ws` and M < 128 -/

example : operandRow (wsDesc 64) 5 40 = 69 ∧ operandRow (wsDesc 64) 5 31 = 5 := by decide
example : operandRow (wsDesc 32) 5 63 = 101 ∧ operandRow (wsDesc 32) 5 15 = 5 := by decide
example : operandRow (wsDesc 32) 31 48 = 127 := by decide
example : operandRow (wsDesc 128) 5 63 = 5 := by decide
-- Without `.ws` the row is the output row.
example : operandRow { wsDesc 64 with ws := false } 5 63 = 5 := by decide
-- Every output's operand row is a lane: below 128.
example : ∀ row < 32, ∀ col < 64, operandRow (wsDesc 32) row col < 128 := by decide
example : ∀ row < 64, ∀ col < 64, operandRow (wsDesc 64) row col < 128 := by decide
example : Operand.rows .a (wsDesc 32) = 128 ∧ Operand.rows .a (wsDesc 64) = 128 ∧
    Operand.rows .a (wsDesc 128) = 128 ∧ Operand.rows .b (wsDesc 32) = 64 := by decide
example : Operand.rows .a { wsDesc 64 with ws := false } = 64 := by decide
example : Operand.bytes .a (wsDesc 32) = 128 * 32 ∧ Operand.bytes .b (wsDesc 32) = 64 * 32 := by
  decide

/-! ## Shared A: lane `L` reads row `L % M` -/

private def k8 : TcShared.Descriptor := ⟨5120, 128, 256, 0, false, false, .none⟩
private def wsSpec (m : Nat) : OperandSpec := ⟨wsDesc m, k8, k8, 2, 2, none, {}⟩
example : (wsSpec 32).byteLoc .a (32 * 69 + 3) = (wsSpec 32).byteLoc .a (32 * 5 + 3) := by decide
example : (wsSpec 64).byteLoc .a (32 * 69 + 3) = (wsSpec 64).byteLoc .a (32 * 5 + 3) := by decide
example : ((wsSpec 32).byteLoc .a (32 * 127 + 31)).isSome = true := by decide
example : (wsSpec 32).byteLoc .a (32 * 128) = none := by decide
example : ∀ index < 32, ((wsSpec 64).byteLoc .a (32 * 100 + index)).isSome = true := by decide
-- Shared A has no Tensor Memory cells.
example : aCell (wsSpec 32) 0 = none := rfl

/-! ## Tensor Memory A: lane `L` holds A row `L` (the probe stores row `l` at lane `l`, columns
64..71) -/

private def wsTs (m : Nat) : OperandSpec := { wsSpec m with aTmem := some 64 }
example : aCell (wsTs 32) (32 * 69 + 6) = some (⟨2, 69, 65⟩, 2) := by decide
example : aCell (wsTs 64) (32 * 127 + 31) = some (⟨2, 127, 71⟩, 3) := by decide
example : aCell (wsTs 128) (32 * 9 + 22) = some (⟨2, 9, 69⟩, 2) := by decide
example : aCell (wsTs 32) (32 * 128) = none := by decide
example : ∀ index < 32, (aCell (wsTs 32) (32 * 77 + index)).map (·.1.lane) = some 77 := by decide
example : (wsTs 32).byteLoc .a 0 = none := by decide
-- `.ws` with M < 128 needs lane field 0.
example : aCell { wsTs 32 with aTmem := some (16 * 2 ^ 16 + 64) } 0 = none := by decide
-- The full A read of every shape has a cell.
example : ∀ index < 32, (aCell (wsTs 32) (32 * 127 + index)).isSome = true := by decide

/-! ## Values: output `(i, j)` uses A row `operandRow` -/

example (a b : List (Option Byte)) : eval [] (wsDesc 32) false a b none 5 40 =
    intEval true true false false a b none (5 + 32 * 2) 40 := rfl
example (a b : List (Option Byte)) : eval [] (wsDesc 64) true a b none 5 40 =
    intEval true true false true a b none (5 + 64) 40 := rfl
example (a b : List (Option Byte)) : eval [] (wsDesc 128) false a b none 5 40 =
    intEval true true false false a b none 5 40 := rfl

/-! ## The ideal-real rule reads A by lane row too -/

private def ws64 : Descriptor := ⟨.one, .f16 .f16 .f32, 64, 64, false, false, false, false, true⟩
example : operandRow ws64 5 40 = 69 := by decide
-- Wrong operand lengths have no rule.
example (a b : List (Option Byte)) (ha : a.length = 7) (acc : Bool) (old : Option Value) :
    execIdealMma ws64 acc a b old 5 3 = .error .noRule := by
  simp [execIdealMma, ha, Operand.bytes, Operand.rows, Operand.extent, ws64,
    Kind.k, Kind.width, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end
end PTX.Tests.TcMmaWsLanes
