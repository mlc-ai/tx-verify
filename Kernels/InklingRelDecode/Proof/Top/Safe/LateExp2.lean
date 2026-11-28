-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Top.Safe.PWords
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
import Kernels.InklingRelDecode.Proof.Top.Safe.NoRace
import Kernels.InklingRelDecode.Proof.Protocol.Alpha.RoundNi
import Kernels.InklingRelDecode.Proof.Softmax.Export.Exp2Late

@[expose] public section

/-! # The inputs of the software `exp2` are real or `-inf`

The input register of each of the 16 instances holds a shifted score of the window, a number or
`-inf`, at the states the lane reaches (`Softmax.Export.exp2_state`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Assumptions

variable {Q : Params} {L : Launch} {m : Mem0}

/-- **The input of each software `exp2` block is a real or `-inf`**
(`Iface.LateValues.exp2`). -/
theorem Safe.exp2 (hp : Pre Q L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hou : NoUbOutside L X)
    (safe : ¬Race L X) (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X)
    (nub : ¬ Assumptions.inputReadOnly.ub L m X) :
    ∀ g t, g % L.block < 128 → Iface.LaneState L X g t → emuSites.contains t.pc = true →
      t.sub = 0 → t.acc = [] → ∀ asg, matchEmu emuBody (kernel.code.drop t.pc) [] = some asg →
        ∃ x : EReal, readERealOpnd t .f32 (.reg (emuReg asg .x)) = some (.ok x) ∧ x ≠ ⊤ := by
  have hS := Safe.scoreWords hp hX hf hou safe rows init nub
  intro g t lane hl hs _ _ asg hasg
  exact Softmax.Export.exp2_state hp hX hf (hS g)
    (fun lane k mode sent b c recv ok g1 => Protocol.Shared.shfl5_ni hp hX hf (hS) lane g1)
    hl hs asg hasg

end PTX.Kernels.InklingRelDecode.Proof.Top
