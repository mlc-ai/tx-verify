-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.RegionTop
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The epilogue is never left

The instruction before position 2565 is a move, so no event is at 2564; from 2565 on every jump
lands from 2565 on (`LoClosed` with the bound of the epilogue). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow

set_option maxRecDepth 100000

variable {L : Launch}

theorem jumps_2565 : JumpsUp 2565 := by unfold JumpsUp; decide +kernel

/-- **No local step and no event continuation of the kernel leaves the positions from 2565 on.** -/
theorem loClosed_epi : LoClosed kernel Assumptions.all L 2565 :=
  loClosed_of jumps_2565 fun _ t _ _ h hs => by
    obtain ⟨ins, hc, hnl, -⟩ := EventFrame.estep_event_source hs
    have h64 : t.pc = 2564 := by omega
    rw [h64, Flow.code_2564] at hc
    cases hc
    exact absurd hnl (by decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Lib
