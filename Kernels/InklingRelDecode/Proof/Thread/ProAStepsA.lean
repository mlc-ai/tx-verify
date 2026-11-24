-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsOv

@[expose] public section

/-! # The prologue's steps from `setmaxnreg.inc` to the proxy fence (pc 27 to 179) -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

theorem stepAt_setup (P : Inh) (d : D) (hs : d.site.pc < 180) : (code L g P).StepAt d := by
  obtain ⟨s, dt⟩ := d
  pro_steps s except [.ldSk => stepOk_s (step_ldSk rfl)]
    skip_by (dsimp only at hs; exact absurd hs (by decide))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
