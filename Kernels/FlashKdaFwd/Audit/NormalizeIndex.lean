-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormalizeWarp

/-! Bind the square-sum register routes to the thread identifier, shared addresses, branch
and reciprocal square roots in the same fixed-length entry. -/
namespace FlashKda.Normalize
open PTX

def int32 (op : IntOp) (ty : IType) (dst : Nat) (a b : Opnd) : Instr :=
  ⟨none, .int ⟨op, .int ty 32, false, [some dst], [a,b]⟩⟩

def move32 (ty : IType) (dst : Nat) (x : Opnd) : Instr :=
  ⟨none, .move ⟨.scalar, .int ty 32, [some dst], [x]⟩⟩

def rowAddress : List Instr :=
  [int32 .shl .b 291 (.reg 206) (.imm 3), int32 .and .b 292 (.reg 291) (.imm 120),
   int32 .shl .b 293 (.reg 206) (.imm 4), int32 .add .s 294 (.reg 290) (.reg 293)]

def storeRoot (offset : Int) (src : Nat) : Instr :=
  ⟨none, .mem {
    kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
    addr := ⟨.reg 340 32,offset⟩, srcs := [.reg src] }⟩

def inverse (sum temp dst : Nat) : List Instr :=
  [⟨none, .float {
    op := .add, ty := ⟨.f32,1⟩, ftz := true, dsts := [some temp],
    srcs := [.reg sum, .f32imm 0x358637bd] }⟩,
   ⟨none, .float { invRoot with dsts := [some dst], srcs := [.reg temp] }⟩]

def publishRoots : List Instr :=
  [int32 (.setp .ne none) .b 11 (.reg 292) (.imm 0), ⟨some (11,false), .bra 150 false⟩] ++
  inverse 209 333 334 ++ inverse 208 335 336 ++
  [int32 .shr .u 337 (.reg 206) (.imm 2), int32 .and .b 338 (.reg 337) (.imm 60),
   move32 .b 339 (.sharedSym 0), int32 .add .s 340 (.reg 339) (.reg 338),
   storeRoot 16384 336, storeRoot 16512 334]

/-- Decode the thread identifier, the shared base, and then the entire unbroken program
from shared-address calculation to storage of the two reciprocal square roots. -/
def normalizeProgram : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[9]!).toOption
  let decodeAt := fun start len =>
    (Decode.code p.env start ((p.instrs.drop start).take len)).toOption
  return (← decodeAt 29 1) ++ (← decodeAt 67 1) ++ (← decodeAt 76 74)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 6000000 in
theorem production_normalize : normalizeProgram = some
    ([move32 .u 206 (.sreg ⟨.tid,some .x⟩), move32 .b 290 (.sharedSym 0)] ++
      rowAddress ++ laneSquares ++ warpSquares ++ publishRoots) := by rfl

/-- For all 256 computing threads, shared byte addresses select 8 consecutive bfloat16
coordinates in one row. Exactly its first thread writes the two 4-byte scale factors. -/
theorem thread_offsets : ∀ tid : Fin 256,
    tid.val <<< 4 = 256*(tid.val/16) + 2*(8*(tid.val%16)) ∧
    ((tid.val <<< 3) &&& 120 = 0 ↔ tid.val%16 = 0) ∧
    (tid.val%16 = 0 → (tid.val >>> 2) &&& 60 = 4*(tid.val/16)) := by decide +kernel

end FlashKda.Normalize
