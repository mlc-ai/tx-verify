-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.Regs

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof

/-- Whether the rescale decision of a sent and a received word skips the rescale: the minimum
and the compare at pc 2256 and 2257, run on a lane that holds only the two words. -/
noncomputable def rescaleSkip (L : Launch) (sent recv : Value) : Bool := Id.run do
  let t : TState := {pc := 2256, regs := fun r =>
    if r = 1544 then some sent else if r = 1545 then some recv else none}
  let some mi := kernel.code[2256]? | return false
  let some cmp := kernel.code[2257]? | return false
  let .ok u := execLocalA Assumptions.all L 0 t mi.op | return false
  let .ok s := execLocalA Assumptions.all L 0 u cmp.op | return false
  return decide (s.regs 170 = some (.pred true))

end PTX.Kernels.InklingRelDecode.Proof.Lib
