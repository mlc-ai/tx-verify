-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.SegPieces

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} (i : Nat) (v : Value)

local macro "advance_site" : tactic => `(tactic| (
  site_step trans [next] seg_by (intro t ht; seg_fp ht using rfl)
    inv_by (intro hi; exact hi) guard_by (first | rfl | trivial)))

theorem dec_step : (code L g regs w).StepAt ⟨.setMaxReg,i,v⟩ := by advance_site
theorem kv_bar_step : (code L g regs w).StepAt ⟨.qkBar,i,v⟩ := by advance_site
theorem p_bar_step : (code L g regs w).StepAt ⟨.pvBar,i,v⟩ := by advance_site
theorem kv_poll_step : (code L g regs w).StepAt ⟨.kvWait,i,v⟩ := by advance_site
theorem p_poll_step : (code L g regs w).StepAt ⟨.pWait,i,v⟩ := by advance_site
theorem final_bar_step : (code L g regs w).StepAt ⟨.finBar,i,v⟩ := by advance_site
theorem final_commit_step : (code L g regs w).StepAt ⟨.finCommit,i,v⟩ := by advance_site
theorem return_bar_step : (code L g regs w).StepAt ⟨.bar1,i,v⟩ := by advance_site
theorem inc_step : (code L g regs w).StepAt ⟨.setMaxRegInc,i,v⟩ := by advance_site

end PTX.Kernels.InklingRelDecode.Proof.Mma
