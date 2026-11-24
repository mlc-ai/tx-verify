-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Ptx
public import Core.Source.Decode
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Transfers
open PTX

def slice (pc count : Nat) : Option (List Instr) := do
  let m := Generated.FlashKdaPacked.module
  let p ← (Decode.prepare m.globals m.functions[0]!).toOption
  (Decode.code p.env pc ((p.instrs.drop pc).take count)).toOption

def add (dst src off : Nat) : Instr := ⟨none, .int {
  op := .add, ty := .int .s 32, dsts := [some dst], srcs := [.reg src, .imm off] }⟩

def literal (dst w value : Nat) : Instr := ⟨none, .move {
  kind := .scalar, ty := .int .b w, dsts := [some dst], srcs := [.imm value] }⟩

def load (i : Nat) : List Instr :=
  let addr := if i = 0 then 498 else 499 + 2*i
  let x := addr + 1
  [add addr 531 (32768 + 4096*i), literal x 32 (8*i)] ++
  (if i = 0 then [literal 2290 64 (2^60)] else []) ++
  [⟨none, .cpTensor true false addr 0 (.reg 2291)
    [.reg x, .reg 499, .reg 500] 496 0 none .tile (some (.reg 2290))⟩]

def store (i : Nat) : List Instr :=
  let addr := if i = 0 then 2054 else 2055 + 2*i
  let x := addr + 1
  [add addr 2089 (32768 + 4096*i), literal x 32 (8*i),
   ⟨none, .cpTensorStore (.reg 3410) [.reg x, .reg 2055, .reg 2056] addr 0 none .tile none⟩]

set_option maxHeartbeats 8000000
set_option maxRecDepth 60000

theorem initial : slice 330 49 = some ((List.range 16).flatMap load) := by rfl

theorem finalStores : slice 3783 52 = some ((List.range 16).flatMap store ++
    [⟨none, .bulkCommit⟩, ⟨none, .bulkWait .read 0⟩, ⟨none, .barSync (.imm 0) true⟩,
     ⟨none, .ret⟩]) := by rfl

end FlashKda.Packed.Transfers
