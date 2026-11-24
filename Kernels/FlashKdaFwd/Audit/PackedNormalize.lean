-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.FullDecode

/-! The two launch modes route normalization through the same lane operations, with
different registers and program counters. -/
namespace FlashKda.Normalize
open PTX

def sites (index : Nat) (counters : List Nat) : Option (List FloatInstr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[index]!).toOption
  counters.mapM fun pc => do
    let stmt ← p.instrs[pc]?
    let [⟨none, .float ins⟩] ← (Decode.code p.env pc [stmt]).toOption | none
    return ins

def firstSquare (src dest : Nat) : FloatInstr :=
  { square with srcs := [.reg src, .reg src, .f32imm 0], dsts := [some dest] }
def rootAt (src dest : Nat) : FloatInstr :=
  { invRoot with srcs := [.reg src], dsts := [some dest] }

set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem fixed_sites : sites 9 [92,141,143] =
    some [firstSquare 271 303, rootAt 333 334, rootAt 335 336] := by rfl

theorem packed_sites : sites 1 [125,174,176] =
    some [firstSquare 276 311, rootAt 341 342, rootAt 343 344] := by rfl

/-- For any supplied lane operands, both kernels give the same local semantics at these sites. -/
theorem same_lanes (inputs : List FVal) :
    (sites 1 [125,174,176]).map (·.map (fun f => f.lane inputs)) =
    (sites 9 [92,141,143]).map (·.map (fun f => f.lane inputs)) := by
  rw [fixed_sites, packed_sites]
  rfl

end FlashKda.Normalize
