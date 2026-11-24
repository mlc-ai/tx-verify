-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.Import
import Core.Sync.MatrixExec

/-! The zero seed, the two interleaved eight-instruction accumulators, and the
conversion of output coordinate (0,0) in the packed and the fixed preparation entry. -/
namespace FlashKda.WarpDot
open PTX

def shape : MmaSpec :=
  { m := 16, n := 8, k := 16,
    types := ⟨.float .bf16,.float .bf16,.float .f32,.float .f32,none⟩ }

/-- Within one 16-coordinate group the four source lanes are 0 to 3 in the warp.
Each lane contributes two adjacent values in both the low and high eight coordinates. -/
theorem fragment_locations : ∀ (h : Fin 2) (l : Fin 4) (p : Fin 2),
    shape.fragA l.val (4*h.val+p.val) = (0,0,8*h.val+2*l.val+p.val) ∧
    shape.fragB l.val (2*h.val+p.val) = (0,8*h.val+2*l.val+p.val,0) ∧
    shape.fragCD (.float .f32) 0 0 = (0,0,0) := by decide +kernel

def untouched (active writes : List Nat) := writes.all fun r => !active.contains r

private structure Accumulators where
  count : Nat
  left : List Nat
  right : List Nat

private def advance (a : Accumulators) (ins : Instr) : Option Accumulators := do
  guard ins.guard.isNone
  let active := a.left ++ a.right
  match ins.op with
  | .int i =>
    guard (untouched active (i.dsts.filterMap id))
    return a
  | .matrix m =>
    match m.op with
    | .move _ => guard (untouched active m.dsts); return a
    | .mma s =>
      let leftTurn := a.count % 2 == 0
      let incoming := if leftTurn then a.left else a.right
      let other := if leftTurn then a.right else a.left
      guard (s == shape && m.srcs.length == 10 && m.dsts.length == 4)
      guard (m.srcs.drop 6 == incoming.map Opnd.reg && untouched other m.dsts)
      if leftTurn then return { a with count := a.count+1, left := m.dsts }
      else return { a with count := a.count+1, right := m.dsts }
    | _ => none
  | _ => none

def region (packed : Bool) : Option Bool := do
  let m := Generated.FlashKdaFwd.module
  let p ← (Decode.prepare m.globals m.functions[if packed then 1 else 9]!).toOption
  let start := if packed then 819 else 763
  let code ← (Decode.code p.env start ((p.instrs.drop start).take 42)).toOption
  let ⟨none,.move seed⟩ :: rest := code | none
  let [some z] := seed.dsts | none
  guard (seed.kind == .scalar && seed.ty == .int .b 32 && seed.srcs == [.imm 0])
  let init := List.replicate 4 z
  let acc ← rest.dropLast.foldlM advance ⟨0,init,init⟩
  let ⟨none,.cvt last⟩ ← rest.getLast? | none
  let first ← acc.left.head?
  let expected : CvtInstr := {
    dst := .float .bf16
    src := .float .f32
    rnd := some .rn
    d := last.d
    srcs := [.reg first]
  }
  return acc.count == 16 && last == expected

set_option maxRecDepth 80000 in
set_option maxHeartbeats 20000000 in
theorem decoded (packed : Bool) : region packed = some true := by cases packed <;> rfl

end FlashKda.WarpDot
