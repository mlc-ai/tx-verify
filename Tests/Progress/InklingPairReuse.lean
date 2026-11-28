-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

namespace PTX.Kernels.InklingRelDecode.Proof.Tests
open PTX PTX.Flow PTX.Proof

private def launch : Launch := {grid := 1, block := 256, params := fun _ => none}

private def scratch (g : Nat) : TState :=
  {pc := 2250, regs := fun r =>
    if r=1533 then some (b32 (212992+(g/32%4)*4)) else if r=1534 then some (b32 7) else none}

private def writeEvent (offset : Nat) : Event :=
  ⟨2250,.wr {loc := ⟨.shared,0,offset⟩,size := 4} (b32 7).toBytes⟩

/-- The address registers in the witnesses are the Softmax control values for the
first lanes of warps 0 and 1, for every entry payload and iteration. -/
example (ent : Softmax.Control.Entry) (d : Softmax.Control.D) :
    (scratch 0).regs 1533 = some (Softmax.Control.valueOf ent launch 0 d 1533) ∧
    (scratch 32).regs 1533 = some (Softmax.Control.valueOf ent launch 32 d 1533) :=
  ⟨rfl,rfl⟩

/-- Evaluate the decoded instruction against Core's firing semantics. Each
write covers a full word of the pair. Its successor advances to PC 2251. -/
theorem scratch_fires_on_pair : ∃ ins, kernel.code[2250]?=some ins ∧ ins.guard=none ∧
    Fires 2250 (eventTmpl Assumptions.all launch 0 (scratch 0) ins.op)
      (writeEvent 212992) (some {(scratch 0) with pc := 2251}) ∧
    Fires 2250 (eventTmpl Assumptions.all launch 32 (scratch 32) ins.op)
      (writeEvent 212996) (some {(scratch 32) with pc := 2251}) :=
  ⟨_, Flow.code_2250, rfl, ⟨rfl,rfl⟩, ⟨rfl,rfl⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Tests
