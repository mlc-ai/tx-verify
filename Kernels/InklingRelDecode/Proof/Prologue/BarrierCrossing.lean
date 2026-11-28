-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

private def head : Site → Bool
  | .sMax | .ld _ | .el _ | .init _ | .fnc0 | .bar2 => true
  | _ => false

private theorem before (s : Site) : s.pc≤180 → head s := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem crosses_barrier {Q L g d e dn} (step : Control.next Q L g d e=some (some dn))
    (lo : d.site.pc≤180) (hi : 180<dn.site.pc) : d.site=.bar2 := by
  obtain ⟨s,a,b,c,w,v⟩ := d
  have pre := before s lo
  have low : ∀ i, (afterInit i).pc≤180 ∧ (Site.init i).pc≤180 := by decide
  cases s <;> try contradiction
  case sMax => cases step; exfalso; dsimp only at hi; revert hi; decide
  case fnc0 => cases step; exfalso; dsimp only at hi; revert hi; decide
  case bar2 => rfl
  case ld i =>
    fin_cases i <;> simp only [Control.next] at step <;> split at step <;> cases step
    all_goals exfalso; dsimp only at hi; revert hi; decide
  case init i => cases step; exact False.elim ((low i).1.not_gt hi)
  case el i =>
    simp only [Control.next] at step
    split at step <;> try contradiction
    cases step
    split at hi
    · exact False.elim ((low i).2.not_gt hi)
    · exact False.elim ((low i).1.not_gt hi)

end PTX.Kernels.InklingRelDecode.Proof.Prologue
