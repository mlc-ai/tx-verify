-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
import Kernels.InklingRelDecode.Gen.StepDispatch
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Proof PTX.Flow

variable {L : Launch} {g first round : Nat} {regs : Nat → Value} {x : BitVec 64}

local macro "dispatch_issue" : tactic => `(tactic| (
  site_step trans [next] seg_by (intro t h; seg_fp h using (first | rfl | simp only [valueOf]))
    inv_by (intro _ h; cases h) guard_by (first | trivial | fail "expected an unguarded site")))

theorem head_step : (code L g regs x first).StepAt ⟨.head, round⟩ := by
  dispatch_issue

theorem idleDec_step : (code L g regs x first).StepAt ⟨.idleDec, round⟩ := by
  dispatch_issue

theorem idleSync_step : (code L g regs x first).StepAt ⟨.idleSync, round⟩ := by
  dispatch_issue

theorem idleSyncAgain_step : (code L g regs x first).StepAt ⟨.idleSyncAgain, round⟩ := by
  dispatch_issue

theorem idleInc_step : (code L g regs x first).StepAt ⟨.idleInc, round⟩ := by
  dispatch_issue

theorem badSync_step : (code L g regs x first).StepAt ⟨.badSync, round⟩ := by
  dispatch_issue

theorem loaderEntry_step : (code L g regs x first).StepAt ⟨.loaderEntry, round⟩ := by
  dispatch_issue

theorem mmaEntry_step : (code L g regs x first).StepAt ⟨.mmaEntry, round⟩ := by
  dispatch_issue

theorem badSyncAgain_step : (code L g regs x first).StepAt ⟨.badSyncAgain, round⟩ := by
  dispatch_issue

theorem sync_step : (code L g regs x first).StepAt ⟨.sync, round⟩ := by
  dispatch_issue

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem exitSync_step : (code L g regs x first).StepAt ⟨.exitSync, round⟩ := by
  by_cases h : g % L.block < 32
  · site_step trans [next, h] seg_by (intro t ht; seg_fp ht using rfl)
      inv_by (intro _ _; exact h) guard_by (trivial)
  · site_step trans [next, h] seg_by (intro t ht; seg_fp ht using (simp [valueOf, h]))
      inv_by (intro _ h; cases h) guard_by (trivial)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem exitDealloc_step : (code L g regs x first).StepAt ⟨.exitDealloc, round⟩ := by
  site_step trans [next] seg_by (intro t ht; seg_fp ht using rfl)
    inv_by (intro _ h; cases h)
    guard_by (rename_i hi; simp [valueOf, hi rfl])

theorem ret_step : (code L g regs x first).StepAt ⟨.ret, round⟩ := by
  refine ⟨fun _ => ⟨_, Flow.code_2855, rfl, trivial⟩, ?_⟩
  intro t e u ins _ _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2855)
  cases hf.2

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
