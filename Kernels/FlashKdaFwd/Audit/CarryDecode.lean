-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Ptx
import Core.Source.Decode

namespace FlashKda.Carry
open PTX

/-- Entry 11 is the fixed-length recurrence with FP32 input and output state.
Program counter 2338 is the first fused multiply-add at the state update on source line 722. -/
def site : Option Instr := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[11]!).toOption
  let source ← p.instrs[2338]?
  let .ok [instruction] := Decode.code p.env 2338 [source] | none
  return instruction

def update : FloatInstr :=
  { op := .fma, ty := ⟨.f32, 1⟩, rnd := some .rn, ftz := true
    dsts := [some 2084], srcs := [.reg 2084, .reg 1887, .reg 1555] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem decode_update : site = some ⟨none, .float update⟩ := by rfl

end FlashKda.Carry
