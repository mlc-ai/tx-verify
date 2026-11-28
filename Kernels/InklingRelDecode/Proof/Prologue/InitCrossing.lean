-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX PTX.Flow Control

private def initHead : Site → Bool
  | .sMax | .ld _ | .el _ | .init _ => true
  | _ => false

private theorem before (s : Site) : s.pc≤178 → initHead s := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- Crossing an initializer PC in the winning lane must execute that initializer.
This holds for each of the twelve independently of the election result payload in other lanes. -/
theorem crosses_init {Q L g d e dn} (step : Control.next Q L g d e=some (some dn))
    (winner : ∀ mask inst l, e.kind=.elect mask inst l → l=laneOf L g)
    (warp : g%L.block<32) (j : Fin 12) (lo : d.site.pc ≤ initPc j) (hi : initPc j<dn.site.pc) :
    d.site=.init j := by
  obtain ⟨s,a,b,c,w,v⟩ := d
  change s.pc ≤ initPc j at lo
  have bound : initPc j≤178 := (by decide : ∀ j : Fin 12, initPc j≤178) j
  have head := before s (by omega)
  cases s <;> try contradiction
  case sMax =>
    cases step
    exact False.elim ((by decide : ∀ j : Fin 12, ¬initPc j<(Site.ld 0).pc) j hi)
  case ld i =>
    fin_cases i <;> simp only [Control.next] at step <;> split at step <;> try contradiction
    all_goals cases step
    all_goals first
      | exact False.elim ((by decide : ∀ j : Fin 12, ¬initPc j < (Site.ld 1).pc) j hi)
      | exact False.elim ((by decide : ∀ j : Fin 12, ¬initPc j < (Site.ld 2).pc) j hi)
      | exact False.elim ((by decide : ∀ j : Fin 12, ¬initPc j < (Site.el 0).pc) j hi)
  case el i =>
    simp only [Control.next] at step
    split at step <;> try contradiction
    rename_i mask inst l kd
    rw [winner _ _ _ kd] at step
    simp only [beq_self_eq_true,decide_eq_true warp,Bool.true_and,ite_true] at step
    cases step
    have no : ∀ i j : Fin 12, (Site.el i).pc ≤ initPc j → ¬initPc j < (Site.init i).pc := by decide
    exact False.elim (no i j lo hi)
  case init i =>
    cases step
    have eq : ∀ i j : Fin 12, initPc i ≤ initPc j → initPc j<(afterInit i).pc → i=j := by decide
    rw [eq i j lo hi]

end PTX.Kernels.InklingRelDecode.Proof.Prologue
