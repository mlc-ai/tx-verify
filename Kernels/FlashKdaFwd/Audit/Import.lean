-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Ptx
public import Core.Source.Decode

/-! Freeze the compilation target and count the instructions of every imported entry. -/
@[expose] public section
namespace FlashKda.Import
open PTX Syntax

theorem target : Decode.target Generated.FlashKdaFwd.module.directives = .ok () := by rfl

mutual
  def instructions : Statement → Nat
    | .scope body => bodyInstructions body
    | .instruction .. => 1
    | _ => 0
  def bodyInstructions : List Statement → Nat
    | [] => 0
    | s :: rest => instructions s + bodyInstructions rest
end

def counts := Generated.FlashKdaFwd.module.functions.map (fun f => bodyInstructions f.body)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem entries : counts =
    [173, 1323, 2528, 3835, 2445, 2500, 2473, 3189, 3091, 1267, 2345, 3653,
     2262, 2316, 2291, 3007, 2909] := by rfl

theorem total : counts.length = 17 ∧ counts.sum = 41607 := by rw [entries]; decide

end FlashKda.Import
