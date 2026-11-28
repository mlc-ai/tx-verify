-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open Control

/-- Lexicographic instruction order with a place for each substep of a vector store. -/
def Site.rank (s : Site) := 4*s.pc+s.sub

private theorem query_lower (t : Nat) (d : D) (k : Nat) (hk : k≤3) :
    4*(388+32*k) ≤ (querySite t d k).rank := by
  unfold querySite
  split_ifs <;> simp_all [Site.rank,Site.pc,Site.sub] <;> omega

private theorem copy_forward (t n : Nat) (d : D) (b : Fin 3) (j : Fin 4) :
    (Site.ptc b j).rank < (afterCopy d t n b j).rank := by
  have h := query_lower t d 0 (by decide)
  fin_cases b <;> fin_cases j <;> simp +decide only [afterCopy, ↓reduceDIte, ↓reduceIte] <;>
    repeat' split
  all_goals first | decide +kernel | (apply Nat.lt_of_lt_of_le _ h; decide)

private theorem query_forward (t : Nat) (d : D) (j : Fin 64) :
    (Site.ldq j).rank < (afterQuery d t j).rank := by
  unfold afterQuery
  split <;> rename_i h
  · split <;> rename_i m
    · have := query_lower t d ((j.val+1)/16) (by omega)
      change 4*(388+2*j.val)+0 < _
      omega
    · change 4*(388+2*j.val)+0 < 4*(388+2*(j.val+1))+0
      omega
  · change 4*(388+2*j.val)+0 < 4*526+0
    omega

theorem rank_next {Q L g d e dn} (hn : Control.next Q L g d e = some (some dn)) :
    d.site.rank < dn.site.rank := by
  obtain ⟨s,a,b,c,w⟩ := d
  cases s with
  | ld i =>
    fin_cases i <;> simp only [Control.next] at hn <;> split at hn <;>
      cases hn <;> dsimp only <;> decide
  | el i =>
    simp only [Control.next] at hn
    split at hn <;> try contradiction
    cases hn
    split
    · revert i; (dsimp only; decide +kernel)
    · revert i; (dsimp only; decide +kernel)
  | init i =>
    cases hn
    revert i; (dsimp only; decide +kernel)
  | bar2 =>
    cases hn; split
    · exact Nat.lt_of_lt_of_le (by dsimp only; decide) (query_lower _ _ 0 (by decide))
    · dsimp only; decide
  | pb b j =>
    fin_cases j <;> cases hn <;> try split
    all_goals revert b; (dsimp only; decide +kernel)
  | arr b | psh b => cases hn; revert b; (dsimp only; decide +kernel)
  | lb b j => fin_cases j <;> cases hn <;> revert b <;> (dsimp only; decide +kernel)
  | pel b j =>
    simp only [Control.next] at hn
    split at hn <;> try contradiction
    cases hn; split
    · revert b j; (dsimp only; decide +kernel)
    · have h : (Site.pel b j).rank < (Site.ptc b j).rank := by revert b j; decide +kernel
      exact h.trans (copy_forward ..)
  | ptc b j => cases hn; exact copy_forward ..
  | ldq j => cases hn; exact query_forward ..
  | stq i j => cases hn; revert i j; (dsimp only; decide +kernel)
  | st9 j => fin_cases j <;> cases hn <;> dsimp only <;> decide
  | exit => cases hn
  | sMax | fnc0 | fnc1 | st8 | bar18 => cases hn; dsimp only; decide

end PTX.Kernels.InklingRelDecode.Proof.Prologue
