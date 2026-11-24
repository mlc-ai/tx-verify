-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsOv

@[expose] public section

/-! # The prologue's stores of the packed rows and its end (pc 526 to 573) -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

theorem stepAt_stq (P : Inh) (d : D) (hs : 520 ≤ d.site.pc) : (code L g P).StepAt d := by
  obtain ⟨s, dt⟩ := d
  pro_steps s except [.stq0_3 => stepOk_q step_stq0_3,
      .stq1_3 => stepOk_q step_stq1_3,
      .stq2_3 => stepOk_q step_stq2_3,
      .stq3_3 => stepOk_q step_stq3_3,
      .stq4_3 => stepOk_q step_stq4_3,
      .stq5_3 => stepOk_q step_stq5_3,
      .stq6_3 => stepOk_q step_stq6_3]
    skip_by (dsimp only at hs; exact absurd hs (by decide))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
