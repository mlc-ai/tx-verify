-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAStepsOv

@[expose] public section

/-! # The prologue's steps of the K/V preload (pc 180 to 315) -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {L : Launch} {g : Nat}

theorem stepAt_pre (P : Inh) (d : D) (hs : 180 ≤ d.site.pc ∧ d.site.pc < 320) :
    (code L g P).StepAt d := by
  obtain ⟨s, dt⟩ := d
  pro_steps s except [.bar2 => ov_bar2,
      .pel0_0 => stepOk_of (step_pel0_0 rfl),
      .pel1_0 => stepOk_of (step_pel1_0 rfl),
      .pel2_0 => stepOk_of (step_pel2_0 rfl),
      .pel0_3 => stepOk_of (step_pel0_3 rfl),
      .pel1_3 => stepOk_of (step_pel1_3 rfl),
      .pel2_3 => stepOk_of (step_pel2_3 rfl),
      .ptc0_3 => ov_ptc0_3,
      .ptc1_3 => ov_ptc1_3,
      .ptc2_3 => ov_ptc2_3]
    skip_by (dsimp only at hs; exact absurd hs (by decide))

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
