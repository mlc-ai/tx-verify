-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open Control

/-- A guarded initialization or tensor issue uses the election immediately preceding it. -/
def Site.votePc : Site → Option Nat
  | .init i => some (elPc i)
  | .ptc b j => some (pelPc b j)
  | _ => none

private theorem query_vote (t d k) : (querySite t d k).votePc = none := by
  unfold querySite; split_ifs <;> rfl

private theorem after_vote (d t n b j) : (afterCopy d t n b j).votePc = none := by
  fin_cases j <;> simp only [afterCopy] <;> repeat' split
  all_goals first | rfl | exact query_vote ..

private theorem query_step_vote (d t j) : (afterQuery d t j).votePc = none := by
  unfold afterQuery; split_ifs <;> first | rfl | exact query_vote ..

private theorem init_step_vote (i) : (afterInit i).votePc = none := by
  revert i; decide +kernel

private theorem store_step_vote (i j) : (Control.afterStore i j).votePc = none := by
  revert i j; decide +kernel

theorem elect_before {Q L g d e dn pc} (hn : Control.next Q L g d e = some (some dn))
    (whereAt : e.pc=d.site.pc) (use : dn.site.votePc = some pc) :
    e.pc=pc ∧ ∃ mask inst, e.kind = .elect mask inst (laneOf L g) := by
  cases hs : d.site <;> simp only [Control.next,hs] at hn
  all_goals repeat' split at hn
  all_goals try contradiction
  all_goals cases hn
  all_goals dsimp only at use
  all_goals try contradiction
  all_goals try (rw [query_vote] at use; contradiction)
  all_goals try (rw [init_step_vote] at use; contradiction)
  all_goals try (rw [after_vote] at use; contradiction)
  all_goals try (rw [query_step_vote] at use; contradiction)
  all_goals try (rw [store_step_vote] at use; contradiction)
  all_goals
    obtain rfl := Option.some.inj use
    rw [hs] at whereAt
    rename_i mask inst ld fired won
    refine ⟨whereAt,mask,inst,?_⟩
    have leader := (Bool.and_eq_true_iff.mp won).2
    rw [beq_iff_eq] at leader
    rw [leader]
    assumption

end PTX.Kernels.InklingRelDecode.Proof.Prologue
