-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Machine
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

private theorem query_inv (t : Nat) (d : D) (group : Nat) (won : Bool) :
    Inv t {d with site := querySite t d group,elected := won} := by
  unfold querySite
  repeat' split
  all_goals first | exact True.intro |
    (rename_i selected; exact (Bool.and_eq_true_iff.mp selected).2)

private theorem copy_inv (t n : Nat) (d : D) (won : Bool) (b j) :
    Inv t {d with site := afterCopy d t n b j,elected := won} := by
  fin_cases j <;> simp only [afterCopy]
  all_goals repeat' split
  all_goals first | trivial | exact query_inv ..

private theorem query_next (t : Nat) (d : D) (j : Fin 64) (on : queryOn t (j.val/16) d) :
    Inv t {d with site := afterQuery d t j} := by
  unfold afterQuery
  split
  · split
    · exact query_inv t d _ d.elected
    · change queryOn t ((j.val+1)/16) d=true
      rwa [show (j.val+1)/16=j.val/16 by omega]
  · trivial

theorem inv_next {Q L g d dn ev} (hi : Inv (g%L.block) d)
    (move : next Q L g d ev=some (some dn)) : Inv (g%L.block) dn := by
  obtain ⟨s,a,z,c,won,recv⟩ := d
  cases s
  case' ld j => fin_cases j
  case' pb b j => fin_cases j
  case' lb b j => fin_cases j
  case' st9 j => fin_cases j
  all_goals simp only [next] at move
  all_goals repeat' split at move
  all_goals cases move
  all_goals first | trivial | exact hi.2 | exact query_inv .. |
    exact copy_inv .. | exact query_next _ _ _ hi |
    (unfold afterStore; split_ifs <;> trivial) | (unfold afterInit; split <;> trivial) |
    (simp_all [Inv])

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
