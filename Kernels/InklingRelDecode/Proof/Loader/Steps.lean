-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases
import Lemmas.Flow.SegPieces

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof
variable {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value} (i n a b : Value)

local macro "cross" : tactic => `(tactic| (
  site_step trans [next] seg_by (intro t ht; seg_fp ht using rfl)
    inv_by (intro _ h; cases h) guard_by (trivial)))

theorem dec_step : (code L g w regs).StepAt ⟨.dec, i, n, a, b⟩ := by cross

theorem endBar_step : (code L g w regs).StepAt ⟨.endBar, i, n, a, b⟩ := by cross

theorem inc_step : (code L g w regs).StepAt ⟨.inc, i, n, a, b⟩ := by cross

theorem warpBar_step (pair : Fin 4) :
    (code L g w regs).StepAt ⟨.warpBar pair, i, n, a, b⟩ := by
  fin_cases pair <;> cross

local macro "packet_step" : tactic => `(tactic| (
  site_step trans [next, finishPair] seg_by (intro t ht; seg_fp ht using rfl)
    inv_by (intro _ h; cases h) guard_by (rfl)))

theorem copy_first_step (pair : Fin 4) :
    (code L g w regs).StepAt ⟨.copy pair false, i, n, a, b⟩ := by
  fin_cases pair <;> packet_step

theorem copy_second_step (pair : Fin 4) (h : pair.val < 3) :
    (code L g w regs).StepAt ⟨.copy pair true, i, n, a, b⟩ := by
  fin_cases pair <;> first | packet_step | contradiction

theorem elect_pair_step (pair : Fin 4) (h : pair.val < 3) :
    (code L g w regs).StepAt ⟨.elect pair, i, n, a, b⟩ := by
  fin_cases pair <;> first | packet_step | contradiction

theorem poll_step : (code L g w regs).StepAt ⟨.poll, i, n, a, b⟩ := by cross

theorem arrive_step : (code L g w regs).StepAt ⟨.arrive, i, n, a, b⟩ := by
  site_step trans [next] seg_by (intro t ht; seg_fp ht using rfl)
    inv_by (intro _ h; cases h)
    guard_by (rename_i hi; exact congrArg Value.pred (decide_eq_true (hi rfl)))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem readyBar_step : (code L g w regs).StepAt ⟨.readyBar, i, n, a, b⟩ := by
  by_cases hl : laneOf L g = 0
  · site_step trans [next, hl] seg_by (intro t ht; seg_fp ht using rfl)
      inv_by (intro _ _; exact hl) guard_by (trivial)
  · let d : D := ⟨.readyBar, i, n, a, b⟩
    let F := (code L g w regs).facts d
    have hmem : (20, Value.pred false) ∈ F := by
      have ht : valueOf L g w regs d 20 = .pred false := by
        change Value.pred (decide (laneOf L g = 0)) = _
        rw [decide_eq_false hl]
      rw [← ht]
      exact mem_factsFrom (show 20 ∈ Flow.live 2377 by decide)
    have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g) Flow.code_2378 hmem rfl
    site_step trans [next, hl] seg_by (exact skip.comp (n := 3) (fun t ht => by
      dsimp only [F, d, code] at ht
      seg_fp ht using rfl))
      inv_by (intro _ h; cases h) guard_by (trivial)

end PTX.Kernels.InklingRelDecode.Proof.Loader
