-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Mathlib.Tactic

namespace PTX.Tests.Packed128
noncomputable section
private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"q".toList, 2, 128⟩, ⟨"d".toList, 2, 64⟩], labels := [], params := [] }
example : Decode.op env "mov.b128" [.vector [.register "d0", .register "d1"], .register "q0"] =
    .ok (.move ⟨.unpack, .int .b 128, [some 2, some 3], [.reg 0]⟩) := rfl
example : Decode.op env "mov.b128" [.register "q1", .vector [.register "d0", .register "d1"]] =
    .ok (.move ⟨.pack, .int .b 128, [some 1], [.reg 2, .reg 3]⟩) := rfl
example (r : ClcResponse) : joinValue (.slice (.clc r) 0 8) (.slice (.clc r) 8 8) = .clc r := by
  simp [joinValue, Value.bytes]
example (r : ClcResponse) (k : Nat) :
    (Value.slice (.clc r) 8 8).byteAt k = (.clc r, 8 + k) := rfl
example (r s : ClcResponse) (h : r ≠ s) :
    joinValue (.slice (.clc r) 0 8) (.slice (.clc s) 8 8) =
      .pair (.slice (.clc r) 0 8) (.slice (.clc s) 8 8) := by
  simp [joinValue, h]
private def t (r : ClcResponse) : TState := { regs := fun _ => some (.clc r) }
private def splitState (r : ClcResponse) : TState :=
  next (setReg (setReg (t r) 2 (.slice (.clc r) 0 8)) 3 (.slice (.clc r) 8 8))
example (r : ClcResponse) :
    execLocal L 0 (t r) (.move ⟨.unpack, .int .b 128, [some 2, some 3], [.reg 0]⟩) =
    .ok (splitState r) := rfl
example (r : ClcResponse) :
    execLocal L 0 (splitState r) (.move ⟨.pack, .int .b 128, [some 1], [.reg 2, .reg 3]⟩) =
    .ok (next (setReg (splitState r) 1 (.clc r))) := by
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, readValue, readReg, splitState, next, setReg,
    Value.bytes, joinValue]
  rfl
end
end PTX.Tests.Packed128
