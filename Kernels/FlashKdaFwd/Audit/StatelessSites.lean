-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StatelessDecode

/-! Identify the carry conversion and scalar tail store in the real no-state PTX entry. -/
namespace FlashKda.Stateless.Trace
open PTX

def narrow : CvtInstr :=
  { dst := .float .bf16, src := .float .f32, rnd := some .rn, d := 129, srcs := [.reg 1953] }

def lastStore : MemAccess :=
  { kind := .store, space := some .global, sem := .weak, elem := .int .b 16,
    addr := ⟨.reg 2030 64, -8⟩, srcs := [.reg 79] }

def sites : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[12]!).toOption
  [1693,1694,2190].mapM fun pc => do
    let s ← p.instrs[pc]?
    let .ok [ins] := Decode.code p.env pc [s] | none
    return ins

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem decoded : sites = some [⟨none,.float carryUpdate⟩, ⟨none,.cvt narrow⟩,
    ⟨none,.mem lastStore⟩] := by rfl

end FlashKda.Stateless.Trace
