-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.Normalize

namespace FlashKda.Normalize
open PTX

/-- Resolve the full fixed-length preparation entry, including nested scopes and register
numbering. Then decode its two normalization instructions using their actual program counters. -/
def normalizationSites : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[9]!).toOption
  [92, 143].mapM fun pc => do
    let source ← p.instrs[pc]?
    let .ok [instruction] := Decode.code p.env pc [source] | none
    return instruction

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
theorem decode_sites : normalizationSites =
    some [⟨none, .float square⟩, ⟨none, .float invRoot⟩] := by rfl

/-- Relate the instructions decoded in the complete entry to their lane results. -/
theorem production_sites : ∃ a b : FloatInstr,
    normalizationSites = some [⟨none, .float a⟩, ⟨none, .float b⟩] ∧
    a.lane [.fin (2^64), .fin (2^64), .zero false] = some (.val (.inf false)) ∧
    b.lane [.inf false] = some (.val (.zero false)) :=
  ⟨square, invRoot, decode_sites, square_lane, inverse_lane⟩

end FlashKda.Normalize
