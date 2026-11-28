-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

/-- The register request is the first instruction of the role. -/
def requestPhase (s : Site) : Nat := if s = .sMax then 0 else 1

private theorem site_hit (s : Site) : s.pc ∈ Lib.requestPcs ↔ s = .sMax ∨ s = .exit := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem query_phase (t d n) : requestPhase (querySite t d n) = 1 := by
  unfold querySite
  repeat' split
  all_goals rfl

private theorem copy_phase (d t n b j) : requestPhase (afterCopy d t n b j) = 1 := by
  fin_cases j <;> dsimp only [afterCopy]
  all_goals repeat' split
  all_goals first | rfl | exact query_phase ..

private theorem init_phase (i) : requestPhase (afterInit i) = 1 := by
  unfold afterInit
  split <;> rfl

private theorem after_query_phase (d t j) : requestPhase (afterQuery d t j) = 1 := by
  unfold afterQuery
  repeat' split
  all_goals first | rfl | exact query_phase ..

private theorem store_phase (i j) : requestPhase (Control.afterStore i j) = 1 := by
  unfold Control.afterStore
  repeat' split
  all_goals rfl

theorem request_next {Q L g d ev dn} (step : Control.next Q L g d ev = some (some dn)) :
    requestPhase dn.site = requestPhase d.site +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,a,b,c,w⟩ := d
  cases s with
  | ld i | pb _ i | lb _ i | st9 i =>
    fin_cases i <;> simp only [Control.next] at step
    all_goals repeat' split at step
    all_goals cases step
    all_goals rfl
  | _ =>
    simp only [Control.next] at step
    repeat' split at step
    all_goals cases step
    all_goals first
      | rfl
      | exact init_phase ..
      | exact copy_phase ..
      | exact query_phase ..
      | exact after_query_phase ..
      | exact store_phase ..

end PTX.Kernels.InklingRelDecode.Proof.Prologue
