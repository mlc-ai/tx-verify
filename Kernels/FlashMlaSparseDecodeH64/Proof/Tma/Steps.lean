-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
public import Lemmas.Flow.CodeU
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsLens
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.StepsCoord
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IdleEvent

@[expose] public section

/-! # The TMA warp's obligations

Every state of the machine satisfies its UB-tolerant step obligation (`stepAt`): the site files
prove the exact ones by `site_cases`, one declaration per site; the coordinate loads and the
gathers, which read no coordinate fact, are UB-tolerant (`StepsCoord.lean`). A hand-back state
(`leave s`) sits at an event of the idle code and stops following the lane (`stepAt_leave`):
warpgroup 1's idle code follows it from there. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A hand-back state sits at an unguarded event of the idle code and stops. -/
theorem stepAt_leave (d : D) {s : IdleSite} (hs : d.site = .leave s) : (code P L g).StepAt d where
  site _ := by
    show ∃ ins, kernel.code[d.site.pc]? = some ins ∧ _
    rw [hs]
    obtain ⟨ins, hc, hl, hg⟩ := idle_event s
    exact ⟨ins, hc, hl, hg _⟩
  step _ _ _ _ _ := Or.inl (Or.inl (by simp only [code, succ, hs]))

/-- **Every state satisfies its UB-tolerant step obligation** (exact outside the coordinate loads
and the gathers). -/
theorem stepAt (hp : Pre P L m) (d : D) : (code P L g).StepAtU d := by
  cases hs : d.site with
  | elect => exact (stepAt_elect hp d hs).toStepAtU
  | loadTopk => exact (stepAt_loadTopk d hs).toStepAtU
  | loadExtra => exact (stepAt_loadExtra d hs).toStepAtU
  | qWait => exact (stepAt_qWait d hs).toStepAtU
  | storeWait => exact (stepAt_storeWait d hs).toStepAtU
  | coordWait => exact (stepAt_coordWait d hs).toStepAtU
  | rawWait => exact (stepAt_rawWait d hs).toStepAtU
  | coord0 k => exact coord_step k d (.inl hs) (coord_seg hp k)
  | coord1 k => exact coord_step k d (.inr (.inl hs)) (coord_seg hp k)
  | coord2 k => exact coord_step k d (.inr (.inr (.inl hs))) (coord_seg hp k)
  | coord3 k => exact coord_step k d (.inr (.inr (.inr hs))) (coord_seg hp k)
  | gather k => exact gather_step k d hs (gather_seg k d hs)
  | rawArrive => exact (stepAt_rawArrive d hs).toStepAtU
  | coordFree => exact (stepAt_coordFree d hs).toStepAtU
  | outBar => exact (stepAt_outBar d hs).toStepAtU
  | exit => exact (stepAt_exit d hs).toStepAtU
  | leave s => exact (stepAt_leave d hs).toStepAtU

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
