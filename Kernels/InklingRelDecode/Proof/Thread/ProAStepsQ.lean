-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsOv

@[expose] public section

/-! # The prologue's query loads (pc 388 to 514) -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

theorem stepAt_ldq (P : Inh) (d : D) (hs : 320 ≤ d.site.pc ∧ d.site.pc < 520) :
    (code L g P).StepAt d := by
  obtain ⟨s, dt⟩ := d
  pro_steps s except [.ldq15 => stepOk_q step_ldq15,
      .ldq31 => stepOk_q step_ldq31,
      .ldq47 => stepOk_q step_ldq47,
      .ldq63 => stepOk_q step_ldq63]
    skip_by (dsimp only at hs; exact absurd hs (by decide))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
