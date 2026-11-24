-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Audit.PipelineSchedule

/-! The static schedule checks on small programs: they reject entry into the middle of a
round, early exits, long internal branches, re-executed initializations, and parities or
barriers with more than one writer. -/
namespace PTX.Tests.PipelineSchedule
open PTX Kernels.Fp16Gemm8192.Pipeline

private def i (op : Op) : Instr := ⟨none, op⟩
private def nop : Instr := i (.move ⟨.scalar, .int .b 32, [some 5], [.imm 0]⟩)
private def spin (pc : Nat) : List Instr :=
  [i (.mbarWait 4 1 0 (.reg 3)), ⟨some (4, false), .bra (pc + 3) false⟩, i (.bra pc false)]

-- pcs: 0 init parity, 1 v_ptr, 2 barrier, 3–5 spin wait, 6 toggle, 7 back edge to 3.
private def good : List Instr :=
  [i (.move ⟨.scalar, .int .b 32, [some 3], [.imm 0]⟩),
   i (.move ⟨.scalar, .int .b 32, [some 0], [.sharedSym 0]⟩),
   i (.int ⟨.add, .int .u 32, false, [some 1], [.reg 0, .imm 8]⟩)] ++ spin 3 ++
  [i (.int ⟨.xor, .int .b 32, false, [some 3], [.reg 3, .imm 1]⟩), i (.bra 3 false)]

example : RoundLoop good 3 7 = true := by decide
example : RunsOnce good 0 = true := by decide
example : TogglesOnly good 3 0 6 = true := by decide
example : waits good = [(3, some 8, some (.register 3))] := by decide

-- An outside branch into the middle of the round.
example : RoundLoop (good ++ [i (.bra 6 false)]) 3 7 = false := by decide
-- A return inside the round.
example : RoundLoop (good.set 6 (i .ret)) 3 7 = false := by decide
-- A branch out of the middle of the round.
example : RoundLoop (good.set 4 ⟨some (4, false), .bra 8 false⟩) 3 7 = false := by decide
-- A long internal branch could skip the toggle; a skip of three instructions is allowed.
private def padded : List Instr :=
  (good.take 6) ++
    [nop, nop, i (.int ⟨.xor, .int .b 32, false, [some 3], [.reg 3, .imm 1]⟩), i (.bra 3 false)]
example : RoundLoop padded 3 9 = true := by decide
example : RoundLoop (padded.set 4 ⟨some (4, false), .bra 9 false⟩) 3 9 = false := by decide
-- A branch back to the initialization re-runs it.
example : RunsOnce (good ++ [i (.bra 0 false)]) 0 = false := by decide
-- A second writer of the parity makes it neither a literal nor a pure toggle.
example : TogglesOnly (good ++ [i (.move ⟨.scalar, .int .b 32, [some 3], [.imm 1]⟩)]) 3 0 6 =
    false := by decide
example : parityOf (good ++ [i (.move ⟨.scalar, .int .b 32, [some 3], [.imm 1]⟩)]) (.reg 3) =
    some (.register 3) := by
  decide
-- A literal with a single writer is resolved; an immediate operand is itself a literal.
example : parityOf [i (.move ⟨.scalar, .int .b 32, [some 2], [.imm 1]⟩)] (.reg 2) =
    some (.literal 1) := by decide
example : parityOf [] (.imm 0) = some (.literal 0) := by decide
-- A barrier register with two writers has no resolved offset.
example :
    barrierOffset (good ++ [i (.int ⟨.add, .int .u 32, false, [some 1], [.reg 0, .imm 16]⟩)]) 1 =
      none := by
  decide

end PTX.Tests.PipelineSchedule
