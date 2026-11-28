-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

/-- The writer issues the scalar publication and the two halves of the count
pair in three consecutive events before reaching the first publication barrier. -/
def publishTail : Site → Nat
  | .st9 j => 1+j.val
  | .bar18 => 3
  | .exit => 4
  | _ => 0

private theorem query (t d n) : publishTail (querySite t d n)=0 := by
  simp only [querySite]
  split_ifs <;> rfl

private theorem copy (d t n b j) : publishTail (afterCopy d t n b j)=0 := by
  fin_cases j <;> dsimp only [afterCopy] <;> repeat' split
  all_goals first | rfl | apply query

private theorem load (d t i) : publishTail (afterQuery d t i)=0 := by
  simp only [afterQuery]
  split_ifs <;> first | rfl | apply query

private theorem store (k h) : publishTail (Control.afterStore k h)=0 := by
  simp only [Control.afterStore]
  split_ifs <;> rfl

theorem publishTail_next {Q L g d ev dn} (hn : Control.next Q L g d ev = some (some dn)) :
    publishTail dn.site = publishTail d.site +
      (if d.site=.st8 ∨ (∃ j, d.site=.st9 j) ∨ d.site=.bar18 then 1 else 0) := by
  obtain ⟨s,a,b,c,w⟩ := d
  cases s <;> simp only [Control.next] at hn
  all_goals repeat' split at hn
  all_goals first | contradiction | cases hn
  all_goals first
    | rfl
    | apply query
    | apply copy
    | apply load
    | apply store
    | (unfold afterInit; split <;> rfl)
    | (rename_i eq; cases eq; rfl)

/-- Consecutive publication sites, ending at the releasing barrier. -/
def pubSite : Fin 4 → Site
  | 0 => .st8 | 1 => .st9 0 | 2 => .st9 1 | 3 => .bar18

theorem pub_predecessor {Q L g d ev dn} (i : Fin 3)
    (hn : Control.next Q L g d ev = some (some dn)) (site : dn.site = pubSite i.succ) :
    d.site = pubSite i.castSucc := by
  have rank := publishTail_next hn
  rw [site] at rank
  have checked (s : Site) (i : Fin 3) : publishTail (pubSite i.succ) = publishTail s +
      (if s=.st8 ∨ (∃ j, s=.st9 j) ∨ s=.bar18 then 1 else 0) → s=pubSite i.castSucc := by
    revert i
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  exact checked _ i rank

private theorem not_st8_query (t d n) : querySite t d n ≠ .st8 := by
  simp only [querySite]
  split_ifs <;> simp

private theorem not_st8_copy (d t n b j) : afterCopy d t n b j ≠ .st8 := by
  fin_cases j <;> dsimp only [afterCopy] <;> repeat' split
  all_goals first | exact not_st8_query _ _ _ | simp

private theorem not_st8_load (d t i) : afterQuery d t i ≠ .st8 := by
  simp only [afterQuery]
  split_ifs <;> first | exact not_st8_query _ _ _ | simp

private theorem not_st8_store (k h) : Control.afterStore k h ≠ .st8 := by
  simp only [Control.afterStore]
  split_ifs <;> simp

/-- The fence is the only predecessor of the first publication store. -/
theorem fence_predecessor {Q L g d ev dn} (hn : Control.next Q L g d ev = some (some dn))
    (site : dn.site = .st8) : d.site = .fnc1 := by
  obtain ⟨s,a,b,c,w⟩ := d
  cases s <;> simp only [Control.next] at hn
  all_goals repeat' split at hn
  all_goals first | contradiction | cases hn
  all_goals first
    | rfl
    | (exfalso; revert site; simp only; apply not_st8_query)
    | (exfalso; revert site; simp only; apply not_st8_copy)
    | (exfalso; revert site; simp only; apply not_st8_load)
    | (exfalso; revert site; simp only; apply not_st8_store)
    | (exfalso; revert site; simp [afterInit]; split <;> simp)
    | (exfalso; revert site; simp)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
