-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX

def Site.won : Site → Bool | .copy .. => true | _ => false

private theorem finish_not_won (d : D) (p : Fin 4) : (finishPair d p).site.won = false := by
  fin_cases p <;> first | rfl | (simp only [finishPair]; split <;> rfl)

theorem predecessor_won {L g d e d'} (hz : next L g d e = some (some d'))
    (hw : d'.site.won = true) :
    d.site.won = true ∨ ∃ mask inst, e.kind = .elect mask inst (laneOf L g) := by
  obtain ⟨s,i,v,a,b⟩ := d
  cases s
  all_goals try exact .inl rfl
  case page upper => cases upper <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hz <;> cases hw
  case first => obtain ⟨_,_,_,_,_,rfl⟩ := read_next hz; cases hw
  case second => obtain ⟨_,_,_,_,_,rfl⟩ := read_next hz; cases hw
  all_goals simp only [next] at hz
  all_goals repeat' split at hz
  all_goals try contradiction
  all_goals try (cases hz; done)
  all_goals try (obtain rfl := Option.some.inj (Option.some.inj hz))
  all_goals first
    | exact Or.inr (by rename_i h; rw [h]; exact ⟨_,_,by assumption⟩)
    | contradiction
    | exact (Bool.noConfusion ((finish_not_won _ _).symm.trans hw))

end PTX.Kernels.InklingRelDecode.Proof.Loader
