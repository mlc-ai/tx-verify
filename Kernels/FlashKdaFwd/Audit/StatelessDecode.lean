-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.CarryDecode

namespace FlashKda.Stateless
open PTX

/-- Fixed-length entry with both optional states omitted, instruction number 1693. -/
def carrySite : Option Instr := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[12]!).toOption
  let source ← p.instrs[1693]?
  let .ok [instruction] := Decode.code p.env 1693 [source] | none
  return instruction

def carryUpdate : FloatInstr :=
  { Carry.update with dsts := [some 1953], srcs := [.reg 1953, .reg 1818, .reg 1487] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem decode_carry : carrySite = some ⟨none, .float carryUpdate⟩ := by rfl

end FlashKda.Stateless
