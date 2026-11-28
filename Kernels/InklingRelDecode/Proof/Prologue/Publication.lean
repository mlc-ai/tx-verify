-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
public import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

/-- Both words are stored at phase zero. Only the softmax handoff is at phase one. -/
def publicationPhase (s : Site) : Nat := if s = .exit then 1 else 0

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar18 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem query_phase (t d n) : publicationPhase (querySite t d n) = 0 := by
  unfold querySite
  repeat' split
  all_goals rfl

private theorem copy_phase (d t n b j) : publicationPhase (afterCopy d t n b j) = 0 := by
  fin_cases j <;> dsimp only [afterCopy]
  all_goals repeat' split
  all_goals first | rfl | exact query_phase ..

private theorem init_phase (i) : publicationPhase (afterInit i) = 0 := by
  unfold afterInit
  split <;> rfl

private theorem after_query_phase (d t j) : publicationPhase (afterQuery d t j) = 0 := by
  unfold afterQuery
  repeat' split
  all_goals first | rfl | exact query_phase ..

private theorem store_phase (i j) : publicationPhase (Control.afterStore i j) = 0 := by
  unfold Control.afterStore
  repeat' split
  all_goals rfl

theorem publication_next {Q L g d ev dn} (hn : Control.next Q L g d ev = some (some dn)) :
    publicationPhase dn.site = publicationPhase d.site +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,a,b,c,w⟩ := d
  cases s with
  | ld i | pb _ i | lb _ i | st9 i =>
    fin_cases i <;> simp only [Control.next] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals rfl
  | _ =>
    simp only [Control.next] at hn
    repeat' split at hn
    all_goals cases hn
    all_goals first
      | rfl
      | exact init_phase ..
      | exact copy_phase ..
      | exact query_phase ..
      | exact after_query_phase ..
      | exact store_phase ..

end PTX.Kernels.InklingRelDecode.Proof.Prologue
