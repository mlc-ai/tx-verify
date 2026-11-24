-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Data.Tail

namespace FlashKda.Tail
open PTX

def start (packedMode : Bool) := if packedMode then 434 else 386
def finish (packedMode : Bool) := if packedMode then 505 else 450
def body (packedMode : Bool) := if packedMode then packed else fixed

def imported (packedMode : Bool) : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[if packedMode then 1 else 9]!).toOption
  let beginAt := start packedMode
  (Decode.code p.env beginAt ((p.instrs.drop beginAt).take (finish packedMode-beginAt))).toOption

set_option maxRecDepth 60000 in
set_option maxHeartbeats 12000000 in
theorem decoded (packedMode : Bool) : imported packedMode = some (body packedMode) := by
  cases packedMode <;> rfl

end FlashKda.Tail
