-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.InputTile

/-! The input-copy and shared vector-load instructions in both preparation entries. -/
namespace FlashKda.InputTile
open PTX Normalize

private def selected (packed : Bool) : Option (List Instr) := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[if packed then 1 else 9]!).toOption
  let pcs := if packed then [65,66,74,76,77,100,103,104,105,108,109,110,111,112,113,119]
    else [37,38,46,48,49,71,74,75,78,79,80,86]
  pcs.mapM fun pc => do
    let stmt ← p.instrs[pc]?
    let .ok [i] := Decode.code p.env pc [stmt] | none
    return i

private def copyTile (dst map coords barrier cache : Nat) : Instr :=
  ⟨none, .cpTensor true false dst 0 (.reg map)
    [.reg coords, .reg (coords+1), .reg (coords+2)] barrier 0 none .tile (some (.reg cache))⟩

private def loadEight (addr : Nat) (offset : Int) (word : Nat) : Instr :=
  ⟨none, .mem {
    kind := .load, elem := .int .b 32, vec := 4, sem := .weak,
    space := some (.shared .cta), addr := ⟨.reg addr 32, offset⟩,
    dsts := (List.range 4).map (fun j => some (word+j)) }⟩

private def routing (packed : Bool) : List Instr :=
  let producer := if packed then 262 else 257
  let queryMap := if packed then 1336 else 1289
  let waitBase := if packed then 273 else 268
  let laneAddress := if packed then 302 else 294
  let producerBarrier := producer - 2
  let bytesReg := producer - 1
  [move32 .b bytesReg (.imm 12864),
   ⟨none, .mbarArrive producerBarrier 0 (.reg bytesReg) (.imm 1) false true .cta none⟩,
   copyTile producer queryMap (producer+1) producerBarrier (queryMap+1),
   int32 .add .s (producer+4) (.reg producer) (.imm 4096),
   copyTile (producer+4) (queryMap+2) (producer+1) producerBarrier (queryMap+1),
   ⟨none, .mbarWait (if packed then 1354 else 1304) waitBase 0 (.reg (waitBase+1)) true .cta⟩,
   ⟨none, .fence (.proxy (.async (some (.shared .cta))) none none)⟩,
   ⟨none, .barSync (.imm 0) true⟩] ++
  (if packed then
    [int32 .shr .u 212 (.reg 210) (.imm 4), int32 .shl .b 298 (.reg 210) (.imm 4),
     int32 .and .b 299 (.reg 298) (.imm 240), int32 .shl .b 300 (.reg 212) (.imm 8),
     int32 .or .b 301 (.reg 300) (.reg 299), int32 .add .s 302 (.reg 295) (.reg 301)]
   else [int32 .shl .b 293 (.reg 206) (.imm 4), int32 .add .s 294 (.reg 290) (.reg 293)]) ++
  [loadEight laneAddress 0 (laneAddress+1), loadEight laneAddress 4096 (laneAddress+5)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 8000000 in
/-- Both entries copy to the same query/key offsets that the normalization loads use.
They have different arithmetic for the source thread's offset. -/
theorem decoded (packed : Bool) : selected packed = some (routing packed) := by
  cases packed <;> rfl

/-- The packed entry splits the thread number into row and column before recombining
the corresponding byte offsets. It selects the same bytes as the fixed entry. -/
theorem packed_offset : ∀ tid : Fin 256,
    (((tid.val >>> 4) <<< 8) ||| ((tid.val <<< 4) &&& 240)) = tid.val <<< 4 := by decide +kernel

end FlashKda.InputTile
